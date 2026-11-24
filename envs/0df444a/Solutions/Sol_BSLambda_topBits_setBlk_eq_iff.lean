-- Prove2me | solution 1 for BSLambda.topBits_setBlk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:30.471989+00:00
-- url     : https://prove2.me/submissions/ef00f2c5-aff7-489e-8435-cf5ef40e92ed

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_topBits_setBlk_apply_self
public import Theorems.Thm_BSLambda_topBits_setBlk_apply_of_ne

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
variable [DecidableEq W]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) (x : Input (W × V)) (w : W) {c : Input W}
    (hc : ∀ w' : W, w' ≠ w → topBits g x w' = c w') (z : Input V) :
    topBits g (setBlk x w z) = c ↔ g z = c w := by
  refine ⟨fun h ↦ by rw [← topBits_setBlk_apply_self g x w z, h], fun h ↦ funext fun w' ↦ ?_⟩
  rcases eq_or_ne w' w with rfl | hw'
  · rw [topBits_setBlk_apply_self, h]
  · rw [topBits_setBlk_apply_of_ne g x w z hw', hc w' hw']
end BSLambda
