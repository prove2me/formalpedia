-- Prove2me | solution 1 for AvramDividend.Classical.twoSidedExitUpTime_le_observation_of_strict_exceedance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:04:00.154234+00:00
-- url     : https://prove2.me/submissions/4155cc62-9f70-4c43-9c1e-044b8f507879

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The canonical upper first-exit infimum never exceeds any time at which
the process has strictly crossed its upper reserve gap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ω : Ω) (s : ℝ≥0)
    (hs : a - x < X.X s ω) :
    twoSidedExitUpTime X (a - x) ω ≤ (s : ℝ≥0∞) := by
  unfold twoSidedExitUpTime
  exact iInf_le_of_le s (iInf_le_of_le hs le_rfl)
