-- Prove2me | solution 1 for ErlerGross.B3_series_double_integral
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:22:36.777711+00:00
-- url     : https://prove2.me/submissions/4930e07d-ea9e-4125-9efc-a720182a8346

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_B3_series_closed_form
import Theorems.Thm_ErlerGross_B3_double_integral_eval
open Real Filter Topology MeasureTheory

theorem solution :
    HasSum (fun n : ℕ => ErlerGross.b3Term (n + 1))
      ((-1 / 2) * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        (1 - y) / (1 - x ^ 2 * y ^ 3))) := by
  convert ErlerGross.B3_series_closed_form using 1
  rw [ErlerGross.B3_double_integral_eval]
  ring
