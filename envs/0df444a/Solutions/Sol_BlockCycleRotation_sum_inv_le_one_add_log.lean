-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_le_one_add_log
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:40:55.092148+00:00
-- url     : https://prove2.me/submissions/6d9f42ba-7af2-44e6-bf99-027c146364d8

import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

end BlockCycleRotation

open BlockCycleRotation in
/-- `∑_{0<m<a} 1/m ≤ 1 + log a`. -/
theorem solution (a : ℕ) :
    ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log a:= by
  have hsub : Finset.Ico 1 a ⊆ Finset.Icc 1 a := by
    intro x hx
    rw [Finset.mem_Ico] at hx
    rw [Finset.mem_Icc]
    omega
  have h1 : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 a, (1 : ℝ) / (m : ℝ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
    intro i _ _
    positivity
  have h2 : ((harmonic a : ℚ) : ℝ) = ∑ m ∈ Finset.Icc 1 a, (1 : ℝ) / (m : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by simp [one_div]
  calc ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 a, (1 : ℝ) / (m : ℝ) := h1
    _ = ((harmonic a : ℚ) : ℝ) := h2.symm
    _ ≤ 1 + Real.log a := harmonic_le_one_add_log a
