-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_stopped_clock_masked_budget_iff_positive_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:13:31.969408+00:00
-- url     : https://prove2.me/submissions/34301cb1-c8dd-4a08-8a28-e37ba22a441c

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The stopped-clock masked mean bound is exactly a positive-clock excess bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if σ ω = 0 then b else F ω) ∂P) ≤ b ↔
      (∫ ω in {ω : Ω | σ ω ≠ 0}, F ω - b ∂P) ≤ 0 := by
  classical
  have hA : MeasurableSet {ω : Ω | σ ω = 0} :=
    AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
      𝓕 σ hσstop
  simpa [Set.compl_setOf, Set.mem_setOf_eq] using
    (AvramDividend.Classical.avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
      P {ω : Ω | σ ω = 0} hA F hF b)
