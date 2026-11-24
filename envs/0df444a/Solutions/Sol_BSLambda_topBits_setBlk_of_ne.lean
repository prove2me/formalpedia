-- Prove2me | solution 1 for BSLambda.topBits_setBlk_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:20:15.217483+00:00
-- url     : https://prove2.me/submissions/ef28cd81-59ad-4255-b85f-7422c340e20b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_topBits_setBlk_apply_self
public import Theorems.Thm_BSLambda_topBits_setBlk_apply_of_ne
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
variable [DecidableEq W]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) (x : Input (W × V)) (w : W) (z : Input V)
    (h : g z ≠ g (blk x w)) :
    topBits g (setBlk x w z) = flipSet (topBits g x) {w} := by
  funext w'
  rcases eq_or_ne w' w with rfl | hw
  · rw [topBits_setBlk_apply_self, flipSet_apply_of_mem (Finset.mem_singleton_self w')]
    exact Bool.eq_not_of_ne h
  · rw [topBits_setBlk_apply_of_ne g x w z hw,
      flipSet_apply_of_notMem (Finset.notMem_singleton.mpr hw)]
end BSLambda
