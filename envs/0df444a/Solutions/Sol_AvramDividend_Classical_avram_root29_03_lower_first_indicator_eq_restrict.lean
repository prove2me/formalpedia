-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_lower_first_indicator_eq_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:26:00.22327+00:00
-- url     : https://prove2.me/submissions/5916c126-9ce1-47f3-988d-3ffec6d234ab

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_lower_before_upper_passage_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For the exact strict lower-first passage event, an indicator integrand
is the original payoff under any measure restricted to that event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) (f : Ω → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω then f ω else 0 ∂μ) =
    (∫⁻ ω in {ω : Ω | twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω}, f ω ∂μ) := by
  have hEvent : MeasurableSet
      {ω : Ω | twoSidedExitDownTime X lower ω <
        twoSidedExitUpTime X upper ω} :=
    chat04_lower_before_upper_passage_event_measurable X lower upper
  simpa only [Set.indicator, Set.mem_setOf_eq] using
    (MeasureTheory.lintegral_indicator hEvent f)
