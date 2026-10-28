-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_discount_lowerfirst_mass_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T12:16:08.413743+00:00
-- url     : https://prove2.me/submissions/fd846a5b-fee6-47ca-b37a-4f6fea2b9387

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_before_upper_passage_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- With zero discount, the lower-before-upper stopped reward equals the strict ruin-first event mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
          ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
            (twoSidedExitDownTime X (-x) ω)))) else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω} :=
    chat04_lower_before_upper_passage_event_measurable X (-x) (a - x)
  simpa [Set.indicator] using
    (MeasureTheory.lintegral_indicator_one (μ := μ) hEvent)
