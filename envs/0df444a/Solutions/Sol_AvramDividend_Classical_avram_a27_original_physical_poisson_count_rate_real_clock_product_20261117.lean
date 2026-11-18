-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:43:43.882829+00:00
-- url     : https://prove2.me/submissions/85439c5b-745c-4c55-a9c8-e6c39d233f29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Converting the original physical Poisson clock/intensity product gives the real count rate. -/
theorem solution (t : ℝ≥0) (markRate : ℝ≥0∞) :
    (((t : ℝ≥0∞) * markRate).toReal) =
      (t : ℝ) * markRate.toReal := by
  simpa using (ENNReal.toReal_mul (a := (t : ℝ≥0∞)) (b := markRate))
