-- Prove2me | solution 1 for ErlerGross.B3_double_integral_eval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:05:34.885264+00:00
-- url     : https://prove2.me/submissions/b81cf073-c7e9-40ea-bd24-cd230f792098

import Mathlib
import Theorems.Thm_ErlerGross_B3_series_double_integral
import Theorems.Thm_ErlerGross_B3_series_closed_form
open Real Filter Topology MeasureTheory

theorem solution :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      (1 - y) / (1 - x ^ 2 * y ^ 3)) = Real.log (27 / 16) := by
  have h := ErlerGross.B3_series_double_integral.unique
    ErlerGross.B3_series_closed_form
  linarith
