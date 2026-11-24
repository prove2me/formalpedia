-- Prove2me | solution 1 for BSLambda.topBits_setBlk_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:53.72794+00:00
-- url     : https://prove2.me/submissions/c0071a28-4d3d-4725-a429-44e599138be7

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
theorem _root_.solution (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z = g (blk x w)) :
    topBits g (setBlk x w z) = topBits g x := by
  refine funext fun w' ↦ ?_
  rcases eq_or_ne w' w with rfl | hw
  exacts [(topBits_setBlk_apply_self g x w' z).trans h, topBits_setBlk_apply_of_ne g x w z hw]
end BSLambda
