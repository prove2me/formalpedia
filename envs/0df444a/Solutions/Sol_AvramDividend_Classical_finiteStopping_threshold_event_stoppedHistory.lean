-- Prove2me | solution 1 for AvramDividend.Classical.finiteStopping_threshold_event_stoppedHistory
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T16:03:39.038565+00:00
-- url     : https://prove2.me/submissions/4d0752f9-ed69-4932-8070-27f417a30b08

import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- An initial clock-threshold event is measurable at the finite stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (c : ℝ≥0) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s]
        ({ω : Ω | τ ω ≤ c} ∩ {ω : Ω | τ ω ≤ s}) := by
  intro s
  have hSet :
      {ω : Ω | τ ω ≤ c} ∩ {ω : Ω | τ ω ≤ s} =
        {ω : Ω | τ ω ≤ min c s} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, le_min_iff]
  rw [hSet]
  exact (𝓕.mono (min_le_right c s)) _ (hτ (min c s))
