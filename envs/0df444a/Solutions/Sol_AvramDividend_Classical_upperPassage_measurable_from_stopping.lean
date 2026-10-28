-- Prove2me | solution 1 for AvramDividend.Classical.upperPassage_measurable_from_stopping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:27:16.301994+00:00
-- url     : https://prove2.me/submissions/971cd1d2-d392-4894-991e-02e2f8703a5c

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_upperPassage_stopping_rightCont_filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The upper-passage stopping time is measurable for the ambient sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (b : ℝ) :
    Measurable (twoSidedExitUpTime X b) := by
  have hs := upperPassage_stopping_rightCont_filtration X b
  exact hs.measurable.mono hs.measurableSpace_le le_rfl
