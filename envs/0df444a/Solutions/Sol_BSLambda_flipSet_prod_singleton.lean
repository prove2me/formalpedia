-- Prove2me | solution 1 for BSLambda.flipSet_prod_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:20:09.341688+00:00
-- url     : https://prove2.me/submissions/59d683c5-2434-42a5-bd91-108688d7bc39

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.iterBlock_zero
attribute [local simp] BSLambda.iterFun_zero
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*}
variable [DecidableEq W]
namespace BSLambda
theorem _root_.solution [DecidableEq V] (x : Input (W × V)) (w : W) (v : V) :
    flipSet x {(w, v)} = setBlk x w (flipSet (blk x w) {v}) := by
  refine blk_injective (funext fun w' ↦ ?_)
  rw [blk_setBlk]
  rcases eq_or_ne w' w with rfl | hw
  · rw [Function.update_self]
    funext v'
    rcases eq_or_ne v' v with rfl | hv
    · simp [blk, flipSet]
    · simp [blk, flipSet, hv, Prod.ext_iff]
  · rw [Function.update_of_ne hw]
    funext v'
    simp [blk, flipSet, hw, Prod.ext_iff]
end BSLambda
