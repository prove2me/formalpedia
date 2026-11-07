-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:46:36.634721+00:00
-- url     : https://prove2.me/submissions/e69cba95-f01f-40d9-8226-fd6d8a692231

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The zero-time atom of a nonnegative stopping clock is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet {ω : Ω | σ ω = 0} := by
  have hσmeas : Measurable (fun ω => (σ ω : WithTop ℝ≥0)) :=
    hσstop.measurable.mono hσstop.measurableSpace_le le_rfl
  have hz : MeasurableSet
      {ω : Ω | (σ ω : WithTop ℝ≥0) = (0 : WithTop ℝ≥0)} :=
    hσmeas (measurableSet_singleton 0)
  simpa only [WithTop.coe_eq_zero] using hz
