-- Prove2me | solution 1 for AvramDividend.Classical.original_lk_negative_mark_cutoff_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:29:21.264242+00:00
-- url     : https://prove2.me/submissions/7ec6b6b4-6825-4090-af5b-39c25a5d258e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_compensated_jump_exponential_primitive
open MeasureTheory Set AvramDividend.Classical

theorem solution (θ y : ℝ) (hθ : 0 < θ) (hy : y < 0) :
    (Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator 1 y) / θ =
    (if y ≤ -1 then y else 0) +
      (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  have hp := compensated_jump_exponential_primitive θ (-y) hθ
  have hm : -θ * -y = θ * y := by ring
  rw [hm] at hp
  by_cases hLarge : y ≤ -1
  · have hout : y ∉ Ioo (-1 : ℝ) 1 := by
      intro hh
      exact (not_lt_of_ge hLarge) hh.1
    simp only [Set.indicator_of_notMem hout, if_pos hLarge, mul_zero, sub_zero]
    rw [hp]
    field_simp [hθ0]
    ring
  · have hin : y ∈ Ioo (-1 : ℝ) 1 := by
      exact ⟨lt_of_not_ge hLarge, by linarith⟩
    simp only [Set.indicator_of_mem hin, Pi.one_apply, mul_one, if_neg hLarge, zero_add]
    rw [hp]
    field_simp [hθ0]
    ring
