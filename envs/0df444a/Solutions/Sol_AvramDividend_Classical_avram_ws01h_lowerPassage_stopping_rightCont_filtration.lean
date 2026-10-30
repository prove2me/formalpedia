-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_lowerPassage_stopping_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:51:53.581992+00:00
-- url     : https://prove2.me/submissions/6b5ad94d-e85a-40b8-b8b8-b3e82b84dc6a

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_lowerCrossingClock_lt_horizon_iff_exists_witness
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The genuine strict lower-passage clock is a stopping time in the
    right-continuous filtration, with no regularity or scale assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (lower : ℝ) :
    IsStoppingTime 𝓕.rightCont (twoSidedExitDownTime X lower) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  have hEq :
      {ω : Ω | twoSidedExitDownTime X lower ω < (t : ℝ≥0∞)} =
      {ω : Ω | ∃ s : ℝ≥0, s < t ∧ X.X s ω < lower} := by
    ext ω
    change
      (⨅ (s : ℝ≥0) (_ : X.X s ω < lower), (s : ℝ≥0∞)) <
        (t : ℝ≥0∞) ↔
      ∃ s : ℝ≥0, s < t ∧ X.X s ω < lower
    exact lowerCrossingClock_lt_horizon_iff_exists_witness X lower ω t
  have hOriginal :
      MeasurableSet[𝓕 t]
        {ω : Ω | twoSidedExitDownTime X lower ω < (t : ℝ≥0∞)} := by
    rw [hEq]
    exact levy_lowerCrossing_before_filtration_measurable X lower t
  exact (𝓕.le_rightCont t) _ hOriginal
