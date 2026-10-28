-- Prove2me | solution 1 for AvramDividend.Classical.chat04_zero_discount_upperfirst_mass_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:19:53.014988+00:00
-- url     : https://prove2.me/submissions/75aa9095-eb68-461e-b949-748e02100fda

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At zero discount the upper-before-ruin reward equals the event mass for every path law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω) (a x : ℝ) :
    (∫⁻ ω, if twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω then
          ENNReal.ofReal (Real.exp (-(0 * ENNReal.toReal
            (twoSidedExitUpTime X (a - x) ω)))) else 0 ∂μ) =
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
    chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  simpa [Set.indicator] using
    (MeasureTheory.lintegral_indicator_one (μ := μ) hEvent)
