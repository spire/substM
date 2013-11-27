{-# LANGUAGE MultiParamTypeClasses
           , FlexibleContexts
           , FlexibleInstances
  #-}

----------------------------------------------------------------------
-- |
-- Module      :  Unbound.LocallyNameless.SubstM
-- License     :  MIT (see LICENSE)
-- Maintainer  :  Nathan Collins <nathan.collins@gmail.com>
--             ,  Larry Diehl <larrytheliquid@gmail.com>
--
-- The @SubstM@ type class for generic capture-avoiding substitution
-- in a monad.  Working in a monad is useful e.g. when implementing
-- hereditary substitution, where substitution must recursively reduce
-- introduced redexes.
--
-- Based on @Unbound.LocallyNameless.Subst@ by Stephanie Weirich and
-- Brent Yorgey.

----------------------------------------------------------------------

module Unbound.LocallyNameless.SubstM (SubstM(..)) where
import Control.Monad (foldM)
import Generics.RepLib
import Unbound.LocallyNameless.Types
import Unbound.LocallyNameless.Alpha

----------------------------------------------------------------------

type SubstMType m b a = Name b -> b -> a -> m a
type SubstHookMType m b a = a -> Maybe (Name b -> b -> m a)

-- | Substitute 'b's into 'a's in the monad 'm'.
class (Monad m, Rep1 (SubstMD m b) a) => SubstM m b a where

  -- | A Generalization of @Unbound.LocallyNameless.Subst.isVar@.
  --
  -- The user should define
  -- 'substHookM' in all cases where a variable is encountered or where
  -- the results of a regular substitution needs to be post processed
  -- (e.g. in hereditary substitution).
  substHookM :: SubstHookMType m b a
  substHookM _ = Nothing

  -- | Single substitution.
  substM :: SubstMType m b a
  substM n u x | isFree n =
     case substHookM x of
       Just f -> f n u
       Nothing -> substMR1 rep1 n u x
  substM m _ _ = error $ "Cannot substitute for bound variable " ++ show m

  -- | Multi substitution.
  --
  -- Note: the default implementation is an *iterated* multi substitution, whereas
  -- @Unbound.LocallyNameless.Subst.substs@ is a *simultaneous* multi
  -- substitution.
  substsM :: SubstM m b a => [(Name b , b)] -> a -> m a
  substsM subs x = foldM (flip . uncurry $ substM) x subs

----------------------------------------------------------------------

data SubstMD m b a = SubstMD {
  substHookMD :: SubstHookMType m b a ,
  substMD :: SubstMType m b a
}

instance (SubstM m b a) => Sat (SubstMD m b a) where
  dict = SubstMD substHookM substM

substDefaultM :: Monad m => Rep1 (SubstMD m b) a => SubstMType m b a
substDefaultM = substMR1 rep1

----------------------------------------------------------------------

substMR1 :: Monad m => R1 (SubstMD m b) a -> SubstMType m b a
substMR1 (Data1 _dt cons) = \ x y d ->
  case (findCon cons d) of
  Val c rec kids ->
      let z = mapM_l (\ w -> substMD w x y) rec kids
      in return . to c =<< z
substMR1 _ = \ _ _ c -> return c

----------------------------------------------------------------------

instance Monad m => SubstM m b Int
instance Monad m => SubstM m b Bool
instance Monad m => SubstM m b ()
instance Monad m => SubstM m b Char
instance Monad m => SubstM m b Integer
instance Monad m => SubstM m b Float
instance Monad m => SubstM m b Double

instance Monad m => SubstM m b AnyName
instance (Monad m, Rep a) => SubstM m b (R a)
instance (Monad m, Rep a) => SubstM m b (Name a)

instance (Monad m, SubstM m c a, SubstM m c b) => SubstM m c (a,b)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d) => SubstM m c (a,b,d)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d, SubstM m c e) => SubstM m c (a,b,d,e)
instance (Monad m, SubstM m c a, SubstM m c b, SubstM m c d, SubstM m c e, SubstM m c f) =>
   SubstM m c (a,b,d,e,f)
instance (Monad m, SubstM m c a) => SubstM m c [a]
instance (Monad m, SubstM m c a) => SubstM m c (Maybe a)
instance (Monad m, SubstM m c a, SubstM m c b) => SubstM m c (Either a b)

instance (Rep order, Rep card, Monad m, SubstM m c b, SubstM m c a, Alpha a,Alpha b) =>
    SubstM m c (GenBind order card a b)
instance (Monad m, SubstM m c b, SubstM m c a, Alpha a, Alpha b) =>
    SubstM m c (Rebind a b)

instance (Monad m, SubstM m c a) => SubstM m c (Embed a)
instance (Alpha a, Monad m, SubstM m c a) => SubstM m c (Rec a)

----------------------------------------------------------------------
