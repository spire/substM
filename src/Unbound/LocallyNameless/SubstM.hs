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
import Control.Applicative
import Control.Monad (foldM)
import Generics.RepLib
import Unbound.LocallyNameless
import Unbound.LocallyNameless.Alpha
import Unbound.LocallyNameless.Types

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
-- | The 'Unbound' library does not support user manipulation of free
-- deBruijn variables. So, we avoid free deBruijn variables by opening
-- all binders; going under them automatically with the generic
-- 'substR1M' via the default 'SubstM' instance would cause capture of
-- deBruijn variables.

instance (Applicative m , Fresh m , Rep order , Rep card ,
          Alpha p , Alpha t , SubstM m b p , SubstM m b t)
  => SubstM m b (GenBind order card p t) where
  substM n u bnd = do
    (p , t) <- unbind bnd
    genBind <$> substM n u p <*> substM n u t
   where
    -- Same as 'Unbound.LocallyNameless.Ops.bind', but with a more
    -- general type signature; this is the left inverse of 'unbind'.
    genBind :: (Alpha p, Alpha t) => p -> t -> GenBind order card p t
    genBind p t = B p (closeT p t)

instance (Applicative m , Fresh m , Alpha p , Alpha q, SubstM m b p ,
          SubstM m b q)
  => SubstM m b (Rebind p q) where
  substM n u bnd = do
    let (p , q) = unrebind bnd
    rebind <$> substM n u p <*> substM n u q

instance (Applicative m , Fresh m , Alpha p , SubstM m b p)
  => SubstM m b (Rec p) where
  substM n u bnd = do
    let p = unrec bnd
    rec <$> substM n u p

-- The analogous instance for 'TRec' fails to type check with
--
--   Could not deduce (Rep1 (SubstDM m b) (TRec p))
--
-- However, Unbound's 'Subst' also has no 'TRec' instance, so maybe
-- there's a reason?
{-
instance (Applicative m , Fresh m , Alpha p , SubstM m b p)
  => SubstM m b (TRec p) where
  substM n u bnd = do
    p <- untrec bnd
    trec <$> substM n u p
-}

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
-- | All Unbound binding constructs need custom instances; the default
-- instance is safe in all other cases, including user defined types.

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

instance (Monad m, SubstM m c a) => SubstM m c (Embed a)

----------------------------------------------------------------------
