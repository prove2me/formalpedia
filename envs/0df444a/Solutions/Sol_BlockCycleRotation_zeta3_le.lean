-- Prove2me | solution 1 for BlockCycleRotation.zeta3_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:43:04.759259+00:00
-- url     : https://prove2.me/submissions/2bc87d69-615a-463b-9c5b-e6320c1137d5

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_tsum_tail_inv_sq
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem uTerm_summable : Summable uTerm := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) := by
    rw [Real.summable_one_div_nat_pow]; norm_num
  refine ((summable_nat_add_iff 1).2 h).congr fun d => ?_
  unfold uTerm
  push_cast
  ring

theorem tsum_uTerm : ∑' d, uTerm d = zeta3 := rfl

theorem uTerm_tail_le : ∑' j : ℕ, uTerm (j + 50) ≤ 1 / 2550 := by
  have hsum : Summable (fun j : ℕ => uTerm (j + 50)) := (summable_nat_add_iff 50).2 uTerm_summable
  have hg : Summable (fun j : ℕ => (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2)) := by
    have h : Summable (fun j : ℕ => 1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by
      have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
        rw [Real.summable_one_div_nat_pow]; norm_num
      refine ((summable_nat_add_iff 51).2 h0).congr fun j => ?_
      push_cast
      ring_nf
    exact h.mul_left _
  have hle : ∀ j : ℕ, uTerm (j + 50) ≤ (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by
    intro j
    unfold uTerm
    have hj : (0 : ℝ) ≤ (j : ℝ) := by positivity
    push_cast
    have hrw : (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2)
        = 1 / (51 * ((50 : ℝ) + (j : ℝ) + 1) ^ 2) := by field_simp
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hj, sq_nonneg ((j : ℝ) + 51), mul_nonneg hj (sq_nonneg ((j : ℝ) + 51))]
  calc ∑' j : ℕ, uTerm (j + 50)
      ≤ ∑' j : ℕ, (1 / 51 : ℝ) * (1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2) :=
        hsum.tsum_le_tsum hle hg
    _ = (1 / 51 : ℝ) * ∑' j : ℕ, 1 / ((50 : ℝ) + (j : ℝ) + 1) ^ 2 := tsum_mul_left
    _ ≤ (1 / 51 : ℝ) * (1 / (50 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h := tsum_tail_inv_sq (n := 50) (by norm_num)
        push_cast at h ⊢
        exact h
    _ = 1 / 2550 := by norm_num

end BlockCycleRotation

open BlockCycleRotation in
set_option maxHeartbeats 1000000 in
-- 50 rational terms of the series for `ζ(3)`.
/-- `ζ(3) ≤ 1.2023`. -/
theorem solution : zeta3 ≤ 12023 / 10000:= by
  have hsplit : (∑ d ∈ Finset.range 50, uTerm d) + ∑' j : ℕ, uTerm (j + 50) = zeta3 := by
    rw [← tsum_uTerm]
    exact uTerm_summable.sum_add_tsum_nat_add 50
  have h1 : ∑ d ∈ Finset.range 50, uTerm d ≤ 12019 / 10000 := by
    norm_num [uTerm, Finset.sum_range_succ]
  linarith [uTerm_tail_le]
