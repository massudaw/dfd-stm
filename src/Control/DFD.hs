{-# LANGUAGE FlexibleContexts,GADTs,ApplicativeDo,
   Arrows,PolyKinds,DataKinds,DeriveFunctor,DeriveAnyClass,AllowAmbiguousTypes,TypeApplications,ScopedTypeVariables,
   RankNTypes,ExistentialQuantification,TypeFamilies #-}
   {-# LANGUAGE TypeOperators #-}
module Control.DFD where

import Control.Concurrent.STM
import qualified Data.Typeable as T
import Type.Reflection 
import GHC.Exts (Constraint)
import Data.Maybe
import Data.Dynamic
import Data.Type.Bool
import Control.Arrow
import Control.Monad
import Control.Arrow.Transformer.Static 
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Foldable as F
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.State


data Operation
  = Create 
  | Update 
  | Delete
  | Read 
  | Init
  | Destroy 
  deriving (Eq,Ord,Show)

data Relation 
  = Equality 
 deriving (Eq,Ord,Show)

data Schema 
 = Schema 
   { vertices :: Map T.TypeRep (Set Operation)
   , edges :: Map (T.TypeRep,T.TypeRep) (Set Relation)
   }
 deriving (Eq,Ord,Show)

instance Semigroup Schema where
 (Schema i e ) <> (Schema j d) = Schema (M.unionWith mappend i j) (M.unionWith mappend e d)
instance Monoid Schema where
 mempty = Schema M.empty M.empty

data Projections a (b ::[*]) where
  ConsProjection :: (a -> c) -> Projections a xs -> Projections  a (c ': xs)
  NilProjection ::  Projections a '[]

class (Typeable a, Ord (Primary a)) => Uniqueness a where
  type Primary a 
  type Refs a :: [*]
  unique :: a -> Primary a
  projection :: Projections a (Refs a)


type Table a = Map (Primary a) a

data GTVar  where
   GTVar :: forall a . Uniqueness a  => TypeRep a -> TVar (Map (Primary a) a) -> GTVar 

data ConstrVar where
   ConstrEquality :: forall a . Uniqueness a  => TypeRep a -> (a -> STM Bool) -> ConstrVar 

fromGTVar
        :: forall a. Typeable a
        => GTVar -- ^ the dynamically-typed object
        -> Maybe (TVar (Map (Primary a) a ))     -- ^ returns: @'Just' a@, if the dynamically-typed
                        -- object has the correct type (and @a@ is its value),
                        -- or 'Nothing' otherwise.
fromGTVar (GTVar t v)
  | Just HRefl <- t `eqTypeRep` rep = Just v
  | otherwise                       = Nothing
  where rep = typeRep :: TypeRep a

fromConstr
        :: forall a. Typeable a
        => ConstrVar -- ^ the dynamically-typed object
        -> Maybe (a -> STM Bool)     -- ^ returns: @'Just' a@, if the dynamically-typed
                        -- object has the correct type (and @a@ is its value),
                        -- or 'Nothing' otherwise.
fromConstr (ConstrEquality t v)
  | Just HRefl <- t `eqTypeRep` rep = Just v
  | otherwise                       = Nothing
  where rep = typeRep :: TypeRep a


data DFDState
 = DFDState { tables :: Map T.TypeRep GTVar 
   , constraints :: Map T.TypeRep (Map T.TypeRep ConstrVar)
   }

newtype SchemaRep a = SchemaRep {getSchemaRep :: (Schema ,a)} deriving (Functor)

instance Applicative SchemaRep where
  pure i = SchemaRep (mempty ,i)
  SchemaRep (a, i) <*> SchemaRep (b, j) = SchemaRep (a <> b, i j )


type DFD a b = StaticArrow SchemaRep (Kleisli (StateT DFDState STM)) a b

getTMap ::  StateT DFDState STM (Map T.TypeRep GTVar)
getTMap = tables <$> get

getCMap ::  StateT DFDState STM (Map T.TypeRep (Map T.TypeRep ConstrVar))
getCMap = constraints <$> get

getTable ::  forall a . (Ord (Primary a),Typeable a, Uniqueness a) => DFD (Primary a) (Maybe a) 
getTable =  
  StaticArrow 
    (SchemaRep 
      (Schema (M.singleton trep (S.singleton Read)) M.empty,
        Kleisli (\i -> do
          v <- getTMap 
          let Just tmap' = M.lookup  trep v 
          lift $ case fromGTVar tmap' of 
            Just tmap ->  do
              M.lookup i<$> readTVar (tmap  :: TVar (Map (Primary a) a)  )
                )))
  where rep = typeRep @a 
        trep = T.typeRep @_ @a T.Proxy


insertRefs :: forall a . (AllHave Uniqueness (Refs a), Ord (Primary a),Typeable a, Uniqueness a) 
           => DFD a (Either String ()) 
insertRefs  = proc i ->  do
    d <- checkDeps (projection @a) -< i
    arr (const "Insertion failed dependencies not met") +++ insert -< d 

delete :: forall a . (Ord (Primary a),Typeable a, Uniqueness a) => DFD a ()
delete =  
  StaticArrow 
    (SchemaRep (Schema (M.singleton trep (S.singleton Delete)) M.empty,
                Kleisli (\i -> do
                  v <- getTMap
                  c <- getCMap
                  let Just tmap' = M.lookup trep v 
                  let cmap' = M.lookup trep c 
                  lift $ case fromGTVar tmap' of 
                    Just tmap ->  do
                      o <- sequenceA $ (\j -> j i )  <$> catMaybes (maybe [] (F.toList . fmap  fromConstr) cmap')
                      if F.all not o 
                         then do
                            var <- readTVar (tmap :: TVar (Map (Primary a) a)  )
                            writeTVar tmap (M.delete (unique i) var)
                         else error "cannot delete"
                        )))
  where rep = typeRep @a 
        trep = T.typeRep @_ @a T.Proxy



insert :: forall a . (Ord (Primary a),Typeable a, Uniqueness a) => DFD a ()
insert =  
  StaticArrow 
    (SchemaRep (Schema (M.singleton trep (S.singleton Create)) M.empty,
                Kleisli (\i -> do
                  v <- getTMap
                  constr <- getCMap
                  let Just tmap' = M.lookup  trep v 
                      tconstr = maybe [] M.toList (M.lookup trep constr)
                  lift $ case fromGTVar tmap' of 
                    Just tmap ->  do
                      var <- readTVar (tmap  :: TVar (Map (Primary a) a)  )
                      writeTVar tmap (M.insert (unique i) i var)
                        )))
  where rep = typeRep @a 
        trep = T.typeRep @_ @a T.Proxy

newTable ::  forall a b . (Ord (Primary a),Typeable a, Uniqueness a) => DFD b ()
newTable  =  do
  StaticArrow 
    (SchemaRep (Schema (M.singleton (T.typeRep ini) (S.singleton Init)) M.empty,
                Kleisli (\i -> do
                  s <- GTVar (typeRep @a) <$> lift (newTVar ini)
                  modify (\i -> i {tables = M.insert (T.typeRep @_ @a T.Proxy ) s (tables i )} )
                  return ()
                        )))
  where ini = M.empty @(Primary a ) @a 

type family IsRef  (u :: [*]) i  where
  IsRef (x ': xs) x = 'True 
  IsRef '[] x        = 'False
  IsRef (x ': xs) y = IsRef xs y
 
type family AllHave (c :: k -> Constraint) (xs :: [k]) :: Constraint
type instance AllHave c '[] = ()
type instance AllHave c (x ': xs) = (c x, AllHave c xs)

checkDeps :: (AllHave Uniqueness xs , Uniqueness a) => Projections a xs -> DFD a (Either String a) 
checkDeps NilProjection = arr Right 
checkDeps (ConsProjection (f :: a -> c)  n) = proc v -> do 
    r <- fmap isJust (getTable @c) -< (unique (f  v)) 
    d <- checkDeps n -< v 
    returnA -< (if r then Right r else Left "Could not validate references"  ) >> d



relation :: forall a c . (Typeable a, Typeable c, Uniqueness a , 'True ~ IsRef (Refs c) a) => (c -> Primary a) ->  DFD () ()
relation f = StaticArrow
    (SchemaRep (Schema M.empty (M.singleton (T.typeRep @_ @a T.Proxy , T.typeRep @_ @c T.Proxy) (S.singleton Equality))
      , Kleisli (\_ -> do 
        tmap <- getTMap 
        let Just tmap' = M.lookup  trep  tmap 
            trep = T.typeRep @_ @c T.Proxy
            op' :: a -> STM Bool
            op' = case fromGTVar tmap' of 
                    Just tmap ->  (\i -> do
                      var <- readTVar (tmap  :: TVar (Map (Primary c) c)  )
                      return (isJust $ F.find ((== unique i). f) var)
                        )
                    Nothing -> error "does not exist"
        modify (\i -> i {constraints = M.insert (T.typeRep @_ @a T.Proxy) 
                                                  (M.singleton 
                                                      (T.typeRep @_ @c T.Proxy ) 
                                                      (ConstrEquality  (typeRep @a) op' )) (constraints i)} ) 
        return () )))

data User  = User 
    { userId :: Int}
    deriving(Eq,Ord,Show)

data Authorization a = Authorization 
    { user :: a 
    , operation :: Operation}
    deriving(Eq,Ord,Show)

type Auth = '[]

instance Uniqueness a => Uniqueness (Authorization a) where
  type Primary (Authorization a) = (Primary a ,Operation) 
  type Refs (Authorization a) = '[a] 
  unique (Authorization i j ) = (unique i,j)
  projection = ConsProjection user NilProjection



instance Uniqueness User where
  type Primary User = Int
  type Refs User = '[]
  unique (User i) = i
  projection = NilProjection

createDB = proc _ -> do
  newTable @User  -< () 
  newTable @(Authorization User) -< ()
  relation @User @(Authorization User) (unique. user) -< ()
  insert -< User 1
  Just u1 <- getTable @User -< 1
  insert -< Authorization u1 Create
  insert -< User 2
  Just u2 <- getTable @User -< 2
  insert -< Authorization u2 Create
  au2 <- getTable @(Authorization User) -< (2,Create)
  u2' <- getTable @User -< 2 
  delete -< Authorization u2 Create
  insertRefs -< Authorization (User 3) Create
  delete -< u2 
  au2' <- getTable @(Authorization User) -< (2,Create)
  returnA -< (au2,au2',u2')

schema v = (fst . getSchemaRep $ unwrap v)
exec v i = atomically $ evalStateT (runKleisli (snd . getSchemaRep $ unwrap v) $ i ) (DFDState M.empty M.empty)

