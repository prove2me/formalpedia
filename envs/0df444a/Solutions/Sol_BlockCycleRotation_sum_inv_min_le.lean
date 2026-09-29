-- Prove2me | solution 1 for BlockCycleRotation.sum_inv_min_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:32:26.792055+00:00
-- url     : https://prove2.me/submissions/efd76d8f-96d6-4cf1-b6bb-ec8735dbe830

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_one_div_min_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

end BlockCycleRotation

open BlockCycleRotation in
/-- **The `log a` factor.**  `∑_{0<m<a} 1/min(m, a-m) ≤ 2 ∑_{0<m<a} 1/m`. -/
theorem solution (a : ℕ) :
    ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ)
      ≤ 2 * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ):= by
  have hrefl : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((a - m : ℕ) : ℝ)
      = ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
    have h := Finset.sum_Ico_reflect (fun j => (1 : ℝ) / (j : ℝ)) 1 (n := a) (Nat.le_succ a)
    simpa using h
  calc ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Ico 1 a, ((1 : ℝ) / (m : ℝ) + 1 / ((a - m : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm' := Finset.mem_Ico.1 hm
        exact one_div_min_le hm'.1 hm'.2
    _ = (∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ))
          + ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((a - m : ℕ) : ℝ) := Finset.sum_add_distrib
    _ = 2 * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by rw [hrefl]; ring
