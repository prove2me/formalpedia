-- Prove2me | solution 1 for BSLambda.topBits_setBlk_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:00.811486+00:00
-- url     : https://prove2.me/submissions/3f9bc1a6-a731-4ea4-9d43-21c22188e012

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
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
    {w' : W} (hw' : w' ≠ w) (h : topBits g x w' ≠ c w') (z : Input V) :
    topBits g (setBlk x w z) ≠ c := by
  refine fun hcon ↦ h ?_
  rw [← topBits_setBlk_apply_of_ne g x w z hw', hcon]
end BSLambda
