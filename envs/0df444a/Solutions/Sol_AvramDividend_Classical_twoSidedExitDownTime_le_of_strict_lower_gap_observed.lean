-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitDownTime_le_of_strict_lower_gap_observed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:10:52.643685+00:00
-- url     : https://prove2.me/submissions/80eb11bb-c0c0-442b-ada1-c59b618e0f63

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The strict lower exit time for a negative reserve gap cannot
exceed an observed crossing time of that same gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : X.X s ω < -x) :
    twoSidedExitDownTime X (-x) ω ≤ (s : ℝ≥0∞) := by
  unfold twoSidedExitDownTime
  exact iInf_le_of_le s (iInf_le_of_le hs le_rfl)
