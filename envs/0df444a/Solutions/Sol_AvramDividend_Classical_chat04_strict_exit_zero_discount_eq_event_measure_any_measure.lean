-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_zero_discount_eq_event_measure_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T14:05:53.71298+00:00
-- url     : https://prove2.me/submissions/79ba9250-ea0c-41a3-8b86-94c10d3cc6f5

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true

/-- The undiscounted upper-before-ruin transform is the measure of its
strict event, for any path-space measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
    chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  simpa [Set.indicator] using
    (MeasureTheory.lintegral_indicator_one (μ := μ) hEvent)
