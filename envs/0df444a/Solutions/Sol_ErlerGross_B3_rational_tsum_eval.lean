-- Prove2me | solution 1 for ErlerGross.B3_rational_tsum_eval
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T16:37:17.305229+00:00
-- url     : https://prove2.me/submissions/59ba4db7-79f1-4325-a4c5-afe2cc2622b9

import Mathlib
import Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form
open Real Filter Topology MeasureTheory

theorem solution :
    tsum (fun n : Nat => (1 : Real) / ((2 * n + 1) * (3 * n + 1) * (3 * n + 2))) =
      Real.log (27 / 16) := by
  simpa using ErlerGross.B3_cubic_reciprocal_series_closed_form.tsum_eq
