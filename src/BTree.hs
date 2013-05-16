
{-# LANGUAGE GADTs, DataKinds, EmptyDataDecls, KindSignatures, ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

-- Copyright Matthew Brecknell 2013
-- Licenced under a Creative Commons Attribution 3.0 Unported Licence
-- http://brck.nl/btree-gadt

module BTree where

import Control.Applicative (Applicative(..),(<$>),(<*>))
import Data.Monoid
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (Traversable(..))
import Test.QuickCheck (quickCheck,verboseCheck,Property,(==>))
import Test.QuickCheck.All (quickCheckAll)
import Data.List (sort)
import qualified Data.List as L

select1 x y lt eq gt
  = case compare x y of { LT -> lt; EQ -> eq; GT -> gt }

select2 x y z xlty xeqy xbtw xeqz xgtz
  = select1 x y xlty xeqy (select1 x z xbtw xeqz xgtz)

t1 a b c = BR (T1 a b c)
t2 a b c d e = BR (T2 a b c d e)

data Foo = Foo

data Nat = Z | S Nat | M | P

data N n a
  = T1 (T n a) a (T n a)
  | T2 (T n a) a (T n a) a (T n a)

data T n a where
  BR :: N n a -> T (S n) a
  LF :: T Z a

data Tree a where
  Tree :: T n a -> Tree a

type Keep t n a = T n a -> t
type Push t n a = T n a -> a -> T n a -> t

insert :: forall a. Ord a => a -> Tree a -> Tree a
insert x (Tree tree) = ins tree Tree (\a b c -> Tree (t1 a b c))
  where
    ins :: forall n t. T n a -> Keep t n a -> Push t n a -> t
    ins LF = \keep push -> push LF x LF

    ins (BR n) = i n
      where
        i :: forall p m. (S p ~ m) => N p a -> Keep t m a -> Push t m a -> t
        i (T2 a b c d e) keep push = select2 x b d xltb xeqb xbtw xeqd xgtd
          where
            xltb = ins a (\k -> keep (t2 k b c d e)) (\p q r -> push (t1 p q r) b (t1 c d e))
            xbtw = ins c (\k -> keep (t2 a b k d e)) (\p q r -> push (t1 a b p) q (t1 r d e))
            xgtd = ins e (\k -> keep (t2 a b c d k)) (\p q r -> push (t1 a b c) d (t1 p q r))
            xeqb = keep (t2 a x c d e)
            xeqd = keep (t2 a b c x e)

        i (T1 a b c) keep push = select1 x b xltb xeqb xgtb
          where
            xltb = ins a (\k -> keep (t1 k b c)) (\p q r -> keep (t2 p q r b c))
            xgtb = ins c (\k -> keep (t1 a b k)) (\p q r -> keep (t2 a b p q r))
            xeqb = keep (t1 a x c)

type Pull t n a = Shrunk n a -> t

data Shrunk (n :: Nat) a where
  H :: T n a -> Shrunk (S n) a

delete :: forall a. Ord a => a -> Tree a -> Tree a
delete x (Tree tree) = search tree Tree shrink
  where
    shrink :: forall n. Shrunk n a -> Tree a
    shrink (H t) = Tree t

    search :: forall n t. T n a -> Keep t n a -> Pull t n a -> t
    search LF keep pull = keep LF

    search (BR (T1 a b c)) keep pull = select1 x b xltb xeqb xgtb
      where
        xltb, xeqb, xgtb :: t
        xltb = search a (\k -> keep (t1 k b c)) (\p -> mrgl p b c)
        xgtb = search c (\k -> keep (t1 a b k)) (\p -> mrg2r keep pull a b p)
        xeqb = repl a (\k r -> keep (t1 k r c)) (\p r -> mrgl p r c) (pull (H a))

        mrgl :: forall p. (S p ~ n) => Shrunk p a -> a -> T p a -> t
        mrgl (H a) b (BR (T1 c d e)) = pull (H (t2 a b c d e))
        mrgl (H a) b (BR (T2 c d e f g)) = keep (t1 (t1 a b c) d (t1 e f g))

    search (BR (T2 a b c d e)) keep pull = select2 x b d xltb xeqb xbtw xeqd xgtd
      where
        xltb = search a (\k -> keep (t2 k b c d e)) (\p -> mrgl p b c d e)
        xbtw = search c (\k -> keep (t2 a b k d e)) (\p -> mrgm a b p d e)
        xgtd = search e (\k -> keep (t2 a b c d k)) (\p -> mrg3r keep a b c d p)
        xeqb = repl a (\k r -> keep (t2 k r c d e)) (\p r -> mrgl p r c d e) (keep (t1 c d e))
        xeqd = repl c (\k r -> keep (t2 a b k r e)) (\p r -> mrgm a b p r e) (keep (t1 a b c))

        mrgl (H a) b (BR (T2 c d e f g)) h i = keep (t2 (t1 a b c) d (t1 e f g) h i)
        mrgl (H a) b (BR (T1 c d e)) f g = keep (t1 (t2 a b c d e) f g)

        mrgm a b (H c) d (BR (T2 e f g h i)) = keep (t2 a b (t1 c d e) f (t1 g h i))
        mrgm a b (H c) d (BR (T1 e f g)) = keep (t1 a b (t2 c d e f g))

    repl :: forall n t. T n a -> Keep (a -> t) n a -> Pull (a -> t) n a -> t -> t
    repl LF keep pull leaf = leaf

    repl (BR (T1 a b c)) keep pull leaf
      = repl c (\k -> keep (t1 a b k)) (\p -> mrg2r keep pull a b p) (pull (H a) b)

    repl (BR (T2 a b c d e)) keep pull leaf =
      repl e (\k -> keep (t2 a b c d k)) (\p -> mrg3r keep a b c d p) (keep (t1 a b c) d)

    mrg2r :: forall p t. Keep t (S p) a -> Pull t (S p) a -> T p a -> a -> Shrunk p a -> t
    mrg2r keep pull (BR (T1 a b c)) d (H e) = pull (H (t2 a b c d e))
    mrg2r keep pull (BR (T2 a b c d e)) f (H g) = keep (t1 (t1 a b c) d (t1 e f g))

    mrg3r :: forall p t. Keep t (S p) a -> T p a -> a -> T p a -> a -> Shrunk p a -> t
    mrg3r keep a b (BR (T2 c d e f g)) h (H i) = keep (t2 a b (t1 c d e) f (t1 g h i))
    mrg3r keep a b (BR (T1 c d e)) f (H g) = keep (t1 a b (t2 c d e f g))

empty :: Tree a
empty = Tree LF

member :: forall a. Ord a => a -> Tree a -> Bool
member x (Tree tree) = mem tree
  where
    mem :: T n a -> Bool
    mem (BR (T1 a b c)) = select1 x b (mem a) True (mem c)
    mem (BR (T2 a b c d e)) = select2 x b d (mem a) True (mem c) True (mem e)
    mem LF = False

fromList :: Ord a => [a] -> Tree a
fromList = L.foldl' (flip insert) empty

instance Foldable Tree where
  foldMap = foldm
    where
      foldm :: forall m a. Monoid m => (a -> m) -> Tree a -> m
      foldm f (Tree t) = fm t
        where
          fm :: forall n. T n a -> m
          fm (BR (T1 a b c)) = fm a <> f b <> fm c
          fm (BR (T2 a b c d e)) = fm a <> f b <> fm c <> f d <> fm e
          fm LF = mempty

instance Show a => Show (Tree a) where
  showsPrec n t = showParen (n > 10) $ showString "fromList " . shows (toList t)

uniq :: Eq a => [a] -> [a]
uniq (x:y:t)
  | x == y = uniq (x:t)
  | otherwise = x : uniq (y:t)
uniq xs = xs

prop_toList :: [Int] -> Bool
prop_toList xs = toList (fromList xs) == uniq (sort xs)

prop_member :: [Int] -> Bool
prop_member xs = all (\x -> member x xt) xs
  where
    xt = fromList xs

prop_not_member :: Int -> [Int] -> Property
prop_not_member x ys = notElem x ys ==> not (member x (fromList ys))

prop_delete :: [Int] -> Bool
prop_delete xs = all (\x -> toList (delete x xt) == L.delete x xu) xs
  where
    xu = uniq (sort xs)
    xt = fromList xs

prop_not_delete :: Int -> [Int] -> Property
prop_not_delete x ys =
  notElem x ys ==> toList (delete x (fromList ys)) == uniq (sort ys)

main = $(quickCheckAll)

