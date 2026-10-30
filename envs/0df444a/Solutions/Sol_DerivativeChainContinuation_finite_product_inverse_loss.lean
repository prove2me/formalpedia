-- Prove2me | solution 1 for DerivativeChainContinuation.finite_product_inverse_loss
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:49:38.677359+00:00
-- url     : https://prove2.me/submissions/3aa560f5-57a3-44eb-9318-34b74085b464

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators


theorem solution {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i) :
    0 ≤ 1-(∏ i ∈ s, (1+x i))⁻¹ ∧
    1-(∏ i ∈ s, (1+x i))⁻¹ ≤ min 1 (∑ i ∈ s, x i) := by
  have hp : 1 ≤ ∏ i ∈ s, (1+x i) := Finset.one_le_prod (fun i hi => by linarith [hx i hi])
  have hi : 0 < (∏ i ∈ s, (1+x i))⁻¹ := inv_pos.mpr (by linarith)
  have hil : (∏ i ∈ s, (1+x i))⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hp
  refine ⟨by linarith, le_min (by linarith) ?_⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hx0 : 0 ≤ x a := hx a (Finset.mem_insert_self _ _)
    have hxs : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hps : 1 ≤ ∏ i ∈ s, (1+x i) := Finset.one_le_prod (fun i hi => by linarith [hxs i hi])
    have his : 0 < (∏ i ∈ s, (1+x i))⁻¹ := inv_pos.mpr (by linarith)
    have hisl : (∏ i ∈ s, (1+x i))⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr hps
    have hax : 1-(1+x a)⁻¹ ≤ x a := by
      apply (sub_le_iff_le_add).mpr
      have hh : (1+x a)*(1+x a)⁻¹=1 := mul_inv_cancel₀ (by linarith)
      nlinarith [sq_nonneg (x a), inv_pos.mpr (by linarith : 0 < 1+x a)]
    have hai : 0 ≤ 1-(1+x a)⁻¹ := by
      have hh := (inv_le_one₀ (by linarith : 0 < 1+x a)).mpr (by linarith : 1 ≤ 1+x a)
      linarith
    have ih' := ih hxs hps his hisl
    simp only [Finset.prod_insert ha, Finset.sum_insert ha, mul_inv_rev]
    nlinarith [mul_le_mul_of_nonneg_right hisl hai]
