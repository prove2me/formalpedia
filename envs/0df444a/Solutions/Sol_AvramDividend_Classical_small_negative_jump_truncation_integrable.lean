-- Prove2me | solution 1 for AvramDividend.Classical.small_negative_jump_truncation_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:26:21.76736+00:00
-- url     : https://prove2.me/submissions/8ff25f17-658b-4ce1-821f-bd00e2dcb396

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (ν : Measure ℝ)
    (hBV : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) < ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal (min (-y) 1) ∂ν) < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun y => ?_) hBV
  exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (neg_le_abs y))

