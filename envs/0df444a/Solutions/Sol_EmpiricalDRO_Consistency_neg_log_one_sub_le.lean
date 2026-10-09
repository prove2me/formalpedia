-- Prove2me | solution 1 for EmpiricalDRO.Consistency.neg_log_one_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T10:51:58.056748+00:00
-- url     : https://prove2.me/submissions/192441fd-7b51-4f42-a4fa-d2f24179e31b

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

theorem solution : ∀ t : ℝ, |t| ≤ 1 / 2 → -Real.log (1 - t) ≤ t + 2 * t ^ 2 := by
  intro t ht
  have h1 : |t| < 1 := by linarith
  have key := Real.abs_log_sub_add_sum_range_le h1 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_add, pow_one, div_one] at key
  have hden : (1 : ℝ) / 2 ≤ 1 - |t| := by linarith
  have hpos : (0 : ℝ) < 1 - |t| := by linarith
  have hsq : |t| ^ (1 + 1) = t ^ 2 := by rw [show (1 + 1 : ℕ) = 2 from rfl, sq_abs]
  rw [hsq] at key
  have hb : t ^ 2 / (1 - |t|) ≤ 2 * t ^ 2 := by
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg t]
  have := (abs_le.mp (key.trans hb)).1
  linarith
