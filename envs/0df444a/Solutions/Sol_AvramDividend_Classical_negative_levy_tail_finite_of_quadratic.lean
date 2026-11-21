-- Prove2me | solution 1 for AvramDividend.Classical.negative_levy_tail_finite_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T21:29:27.642839+00:00
-- url     : https://prove2.me/submissions/4ffc1040-4395-4ea7-b6bf-030737e81095

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ)
    (hQuad : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    ∀ t : ℝ, 0 < t → ν (Iio (-t)) < ⊤ := by
  intro t ht
  have hfin := negative_jump_truncation_measure_finite ν hQuad t ht
  have hsub : Iio (-t) ⊆ Iic (-t) := by
    intro y hy
    exact le_of_lt (show y < -t from hy)
  exact lt_of_le_of_lt (measure_mono hsub) hfin
