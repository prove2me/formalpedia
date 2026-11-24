-- Prove2me | solution 1 for BSLambda.lam_iterFun_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:36.800327+00:00
-- url     : https://prove2.me/submissions/854ea043-cfb8-4cc0-955d-7f403b368065

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_flipSet_singleton_self
public import Theorems.Thm_BSLambda_lam_eq_of_sensAt_eq
public import Theorems.Thm_BSLambda_sensAt_eq_card_univ


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : lam (iterFun f 0) = 1 := by
  let : Unique (IterCoord V 0) := inferInstanceAs (Unique PUnit)
  refine lam_eq_of_sensAt_eq zero_le_one fun x ↦ ?_
  have hsc (v : IterCoord V 0) : SensitiveCoord (iterFun f 0) x v := by
    change flipSet x {v} v ≠ x v
    rw [flipSet_singleton_self]
    exact Bool.not_ne_self _
  rw [sensAt_eq_card_univ hsc, Fintype.card_unique, Nat.cast_one]
end BSLambda
