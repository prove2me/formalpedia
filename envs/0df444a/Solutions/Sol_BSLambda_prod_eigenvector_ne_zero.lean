-- Prove2me | solution 1 for BSLambda.prod_eigenvector_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:32.849411+00:00
-- url     : https://prove2.me/submissions/1964f1a3-af20-4a08-9fcf-aed8e1d0a221

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
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
omit [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) {u : Input V → ℝ} {v : Input W → ℝ}
    (hboth : ∀ β : Bool, ∃ a : Input V, g a = β ∧ u a ≠ 0) (hv : v ≠ 0) :
    (fun x : Input (W × V) ↦ v (topBits g x) * ∏ w, u (blk x w)) ≠ 0 := by
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hb
  choose a ha hua using hboth
  refine Function.ne_iff.mpr ⟨fun p ↦ a (b p.1) p.2, ?_⟩
  simp only [Pi.zero_apply]
  have hbt : topBits g (fun p : W × V ↦ a (b p.1) p.2) = b := funext fun w ↦ ha (b w)
  rw [hbt]
  apply mul_ne_zero hb
  rw [Finset.prod_ne_zero_iff]
  exact fun w _ ↦ hua (b w)
end BSLambda
