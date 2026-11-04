-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_paymentTimes_measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:36:53.353943+00:00
-- url     : https://prove2.me/submissions/f263064f-57b9-43c1-8ac7-4e5bec00a900

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original strict-ruin right-payment selector is Borel measurable. -/
theorem solution (σ : ℝ≥0∞) :
    MeasurableSet (paymentTimes σ) := by
  unfold paymentTimes
  measurability
