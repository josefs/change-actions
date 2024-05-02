{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
module Control.ChangeAction where

import Data.Array
import Data.Maybe
import Data.Monoid

class Monoid (Delta a) => ChangeAction a where
    type Delta a
    act :: a -> Delta a -> a

instance ChangeAction [a] where
    type Delta [a] = [a]
    act = (++)

newtype AMonoid a = AMonoid a
  deriving (Semigroup, Monoid)

instance Monoid a => ChangeAction (AMonoid a) where
    type Delta (AMonoid a) = AMonoid a
    act = (<>)

-- | A change action which doesn't actually change.
-- The first parameter `b` is the delta, and can be any monoid
newtype Empty b a = Empty a

instance Monoid b => ChangeAction (Empty b a) where
    type Delta (Empty b a) = b
    act a _ = a

-- | A change action which uses endo functors as deltas
newtype EndoCA a = EndoCA a

instance ChangeAction (EndoCA a) where
    type Delta (EndoCA a) = Endo a
    act (EndoCA a) (Endo f) = EndoCA (f a)

instance (ChangeAction a, ChangeAction b) => ChangeAction (a,b) where
    type Delta (a,b) = (Delta a, Delta b)
    act (a,b) (da,db) = (act a da, act b db)

instance (ChangeAction a, ChangeAction b) => ChangeAction (Either a b) where
    type Delta (Either a b) = (Delta a, Delta b)
    act (Left a) (da,_) = Left (act a da)
    act (Right b) (_,db) = Right (act b db)

-- | Pointwise change actions on functions
instance ChangeAction b => ChangeAction (a -> b) where
    type Delta (a -> b) = a -> Delta b
    act f df = \x -> act (f x) (df x)

class ChangeAction a => CompleteChangeAction a where
    minus :: a -> a -> Delta a

instance (CompleteChangeAction a, CompleteChangeAction b) =>
  CompleteChangeAction (a,b) where
      minus (a,b) (c,d) = (minus a c, minus b d)

{- The paper claims that Either is complete and differentiable.
   But I don't see how `minus` can be defined in a way that
   fulfils the laws.
instance CompleteChangeAction (Either a b) where
    minus (Left a) (Left b) = (minus a b, mempty)
    minus (Right a) (Right b) = (mempty, minus a b)
    minus (Left a) (Right b) = (mempty,b)
    minus (Right a) (Left b) = (b,mempty)
-}
{-
act a (minus b a) = b

act (Left a) (minus (Left b) (Left a)) =
act (Left a) (minus b a , mempty) =
Left (act a (minus b a)) = b

act (Left a) (minus (Right b) (Left a)) =
act (Left a) (a,mempty) = Left (act a a)
-}

-- Arithmetic Monoids

newtype Add a = Add a

instance Num a => Semigroup (Add a) where
    Add a <> Add b = Add (a + b)

instance Num a => Monoid (Add a) where
    mempty = Add 0

instance Num a => ChangeAction (Add a) where
    type Delta (Add a) = Add a
    act (Add a) (Add b) = Add (a + b)

instance Num a => CompleteChangeAction (Add a) where
    minus (Add a) (Add b) = Add (a - b)

newtype Mult a = Mult a

instance Num a => Semigroup (Mult a) where
    Mult a <> Mult b = Mult (a * b)

instance Num a => Monoid (Mult a) where
    mempty = Mult 1

instance Num a => ChangeAction (Mult a) where
    type Delta (Mult a) = Mult a
    act (Mult a) (Mult b) = Mult (a * b)

instance Fractional a => CompleteChangeAction (Mult a) where
    minus (Mult a) (Mult b) = Mult (a / b)

instance Ix i => ChangeAction (Array i a) where
    -- We have a choice here. We could just have a single tuple
    -- but then we couldn't support `minus`.
    type Delta (Array i a) = [(i,a)]
    act = (//)

instance (Eq a, Ix i) => CompleteChangeAction (Array i a) where
    -- Assume that the arrays have the same indexes. Not great.
    minus arr1 arr2 = mapMaybe check (indices arr1)
      where
        check i
          | arr1 ! i == arr2 ! i = Nothing
          | otherwise = Just (i, arr2 ! i)

{-
Time is a change action with TimeSpan as Delta
-}

--- Derivatives

-- | A function and its derivative
type Prime a b = (a -> b, a -> Delta a -> Delta b)

-- | A terribly inefficient derivative
derivative
  :: (CompleteChangeAction a
     ,CompleteChangeAction b)
  => (a -> b)
  -> a -> Delta a -> Delta b
derivative f = \a da -> f (act a da) `minus` f a

mkPrime
  :: (CompleteChangeAction a
     ,CompleteChangeAction b)
  => (a -> b)
  -> Prime a b
mkPrime f = (f, derivative f)

pi1 :: CompleteChangeAction a => Prime (a,b) a
pi1 = (fst, \(a,_) (da,_) -> act a da `minus` a)
{-
derivative fst =
\(a,b) (da,db) -> fst (act (a,b) (da,db)) `minus` fst (a,b) =
\(a,b) (da,db) -> fst (act a da, act b db) `minus` a =
\(a,_) (da,_) -> act a da `minus` a
-}
pi2 :: CompleteChangeAction b => Prime (a,b) b
pi2 = (snd, \(_,b) (_,db) -> act b db `minus` b)

{-

Functions don't have a minus, so this cannot be written.

index :: Ix i => Prime (Array i a) (i -> a)
index = ((!), \arr darr -> )

derivative (!) =
\arr darr -> (!) (act arr darr) `minus` (!) arr =
\arr darr ->


-}

index' :: (CompleteChangeAction a, CompleteChangeAction i, Ix i)
       => Prime (Array i a,i) a
index' = (uncurry (!)
         ,\(arr,i) (darr,di) ->
            let i' = act i di in
            case lookup i' darr of
                Nothing -> (arr ! i') `minus` (arr!i)
                Just e -> e `minus` (arr!i)
         )
{-
derivative (uncurry (!)) =
\(arr,i) (darr,di) -> uncurry (!) (act (arr,i) (darr,di)) `minus` uncurry (!) (arr,i)
\(arr,i) (darr,di) -> uncurry (!) (act arr darr, act i di) `minus` (arr ! i)
\(arr,i) (darr,di) -> (arr//darr) ! (act i di) `minus` (arr ! i)

`(arr // darr) ! i` can be somewhat improved by not actually performing
the update but go through the `darr` list and as soon as we find the index
well, return the corresponding element.
-}

-- This is different from the one given in the paper
apply :: (ChangeAction a, CompleteChangeAction b)
      => Prime (a -> b, a) b
apply = (uncurry ($)
        ,\(f,a) (df,da) ->
            let b = act a da
            in act (f b) (df b) `minus` f a
        )
{-
derivative (uncurry ($)) =
\(f,a) (df,da) -> uncurry ($) (act (f,a) (df,da)) `minus` uncurry ($) (f,a) =
\(f,a) (df,da) -> (act f df) $ (act a da) `minus` f a
\(f,a) (df,da) -> (\b -> act (f b) (df b)) $ (act a da) `minus` f a =
\(f,a) (df,da) -> let b = act a da in act (f b) (df b) `minus f a
-}

--- Fix points

iter :: Monoid a => (a -> a) -> Int -> a
iter f n = iterate f mempty !! n

iterd2 :: (Monoid a, CompleteChangeAction a)
       => Prime a a -> Int -> Int -> Delta a
iterd2 (f,_f') 0 dn = iter f dn `minus` mempty -- should be bottom
iterd2 p@(f,f') n dn = f' (iter f n) (iterd2 p (n-1) dn)
{-
recur :: Prime a a -> (a, Delta a) -> (a, Delta a)
recur (f,f') (bottom,bottom) = (bottom, f bottom `minus` bottom)
recur (f,f') (a,da) = (act a da, f' a da)
-}

--- Alternative implementation is to parameterize on the monoid

class Monoid a => CA a where
    type Base a
    ac :: Base a -> a -> Base a

instance CA (Endo a) where
    type Base (Endo a) = a
    ac a (Endo f) = f a

{- This instance will break everything due to the type instance

instance {-# OVERLAPPABLE #-} Monoid a => CA a where
    type Base a = a
    ac = (<>)
-}
