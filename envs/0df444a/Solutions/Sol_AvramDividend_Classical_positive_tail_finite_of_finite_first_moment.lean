-- Prove2me | solution 1 for AvramDividend.Classical.positive_tail_finite_of_finite_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:50:04.025375+00:00
-- url     : https://prove2.me/submissions/09a2ad75-f175-4a13-b317-5b5896f049f8

import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_threshold_mass_le_first_moment
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (μ : Measure ℝ≥0)
    (hmoment : (∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ) ∂μ) < ⊤) :
    ∀ t : ℝ, 0 < t →
      μ {z : ℝ≥0 | t < (z : ℝ)} ≠ ⊤ := by
  intro t ht hinf
  have h := AvramDividend.Classical.positive_jump_tail_threshold_mass_le_first_moment μ t ht
  rw [hinf, ENNReal.mul_top (ENNReal.ofReal_pos.2 ht).ne'] at h
  exact absurd (lt_of_le_of_lt h hmoment) (lt_irrefl _)
