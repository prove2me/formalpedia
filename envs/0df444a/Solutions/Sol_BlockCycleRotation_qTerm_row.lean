-- Prove2me | solution 1 for BlockCycleRotation.qTerm_row
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:38:09.946203+00:00
-- url     : https://prove2.me/submissions/cf901004-51d4-4db1-a21b-564b47e66e64

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Remark21
import Theorems.Thm_BlockCycleRotation_tsum_telescope
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

theorem harm_eq_range (n : ℕ) : harm (n + 1) = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) := by
  unfold harm
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring_nf

end BlockCycleRotation

open BlockCycleRotation in
/-- **The row sums give `H_n/n²`.** -/
theorem solution (i : ℕ) : ∑' j : ℕ, qTerm (i, j) = harm (i + 2) / ((i : ℝ) + 1) ^ 2:= by
  have hn : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hc : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
  have heq : ∀ j : ℕ, qTerm (i, j)
      = (1 / ((i : ℝ) + 1) ^ 2)
        * (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + ((i + 1 : ℕ) : ℝ) + 1)) := by
    intro j
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hjn : (0 : ℝ) < (j : ℝ) + ((i : ℝ) + 1) + 1 := by positivity
    rw [hc]
    unfold qTerm
    field_simp
    ring
  rw [tsum_congr heq, tsum_mul_left, tsum_telescope (i + 1), ← harm_eq_range]
  ring
