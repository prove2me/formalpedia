-- Prove2me | solution 1 for BSLambda.lam_iterFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:46:07.67814+00:00
-- url     : https://prove2.me/submissions/228b726d-307a-4a27-86de-754e005e0534

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_lam_comp
public import Theorems.Thm_BSLambda_lam_iterFun_zero

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : ∀ m, lam (iterFun f m) = lam f ^ m
  | 0 => (lam_iterFun_zero f).trans (pow_zero _).symm
  | m + 1 => by
      change lam (comp f (iterFun f m)) = _
      rw [lam_comp, solution f m, pow_succ']
end BSLambda
