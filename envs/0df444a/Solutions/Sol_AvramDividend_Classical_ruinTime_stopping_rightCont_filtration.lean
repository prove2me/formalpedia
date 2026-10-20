-- Prove2me | solution 1 for AvramDividend.Classical.ruinTime_stopping_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:54:50.698731+00:00
-- url     : https://prove2.me/submissions/552b6f40-007d-460d-9926-ad16759b1815

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_strict_event_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/- Source-only dependent next step. DO NOT SUBMIT while imported strict event is Open. -/
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
