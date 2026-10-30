-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exit_expectation_eq_restrict_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:07:28.865984+00:00
-- url     : https://prove2.me/submissions/503bb711-b716-483c-a73b-c0fe180e0f90

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_lower_passage_event_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact strict-exit reward as an ENNReal integral under the original
measure restricted to the measurable upper-first event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a x : ℝ) :
    twoSidedExitExpectation X q a x =
      (∫⁻ ω in {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω},
        ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω)))) ∂P) := by
  have hEvent :
      MeasurableSet {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω} :=
    chat03_upper_before_lower_passage_event_measurable X (-x) (a - x)
  simpa only [twoSidedExitExpectation, Set.indicator, Set.mem_setOf_eq] using
    (MeasureTheory.lintegral_indicator hEvent
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTime X (a - x) ω))))))
