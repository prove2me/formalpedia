-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_ruinTime_rightCont_stopping_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:36:31.620065+00:00
-- url     : https://prove2.me/submissions/d3e65304-ee1a-4bd5-a725-d12e8b7189c1

import Mathlib.Probability.Process.Stopping
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_strict_event_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Same-path controlled ruin time is a stopping time after right-continuous
filtration augmentation; needed for the genuine stopped marked jump kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    IsStoppingTime 𝓕.rightCont (ruinTime X x D) := by
  apply isStoppingTime_of_measurableSet_lt_of_isRightContinuous
  intro t
  exact (𝓕.le_rightCont t) _
    (ruinTime_strict_event_filtration_measurable X x D hD t)
