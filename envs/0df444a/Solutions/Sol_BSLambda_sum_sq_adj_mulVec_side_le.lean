-- Prove2me | solution 1 for BSLambda.sum_sq_adj_mulVec_side_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:01.426565+00:00
-- url     : https://prove2.me/submissions/79443db2-d75e-49da-a34c-9c8cd1a8ed9d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_sum_sq_adj_mulVec_le
public import Theorems.Thm_BSLambda_adj_eq_zero_of_apply_eq
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
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
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (v : Input V → ℝ) (β : Bool) :
    ∑ x, (if f x = β then (adj f *ᵥ v) x else 0) ^ 2
      ≤ lam f ^ 2 * ∑ x, (if f x = β then 0 else v x) ^ 2 := by
  refine (Finset.sum_le_sum fun x _ ↦ ?_).trans
    (sum_sq_adj_mulVec_le f fun z ↦ if f z = β then 0 else v z)
  rcases eq_or_ne (f x) β with hx | hx
  · rw [if_pos hx]
    refine le_of_eq (congrArg (· ^ 2) (Finset.sum_congr rfl fun z _ ↦ ?_))
    rcases eq_or_ne (f z) β with hz | hz
    · simp [adj_eq_zero_of_apply_eq f (hx.trans hz.symm)]
    · simp [hz]
  · rw [if_neg hx, zero_pow two_ne_zero]
    positivity
end BSLambda
