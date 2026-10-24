-- Prove2me | solution 1 for AvramDividend.Classical.chat04_twoSidedExitExpectation_zero_discount_eq_event_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:16:39.927955+00:00
-- url     : https://prove2.me/submissions/fd160e6d-405c-43ca-874a-8cd2a3496bae

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At zero discount, the killed first-passage lower integral is exactly
the probability of the strict upward-before-downward exit event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ) :
    twoSidedExitExpectation X 0 a x =
      P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
    chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  simpa [twoSidedExitExpectation, Set.indicator] using
    (MeasureTheory.lintegral_indicator_one (μ := P) hEvent)
