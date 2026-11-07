-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_tight_positive_excess_le_any_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:15:22.905005+00:00
-- url     : https://prove2.me/submissions/d64974ac-1ef3-41fe-8aa4-cf43e0123cd0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact positive payoff deficit is pointwise dominated by every
    nonnegative error envelope appearing in a valid budget inequality. -/
theorem solution
    (payoff baseline err : ℝ)
    (hbudget : payoff ≤ baseline + max err 0) :
    max (payoff - baseline) 0 ≤ max err 0 := by
  refine max_le ?_ ?_
  · linarith
  · exact le_max_right _ _
