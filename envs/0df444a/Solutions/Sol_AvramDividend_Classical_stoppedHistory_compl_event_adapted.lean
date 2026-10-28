-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_compl_event_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:54:28.60376+00:00
-- url     : https://prove2.me/submissions/e9ffdc20-4b02-45d1-a820-567131d7d5ee

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- Stopped-history events remain measurable after complementation. -/
theorem solution

    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (Aᶜ ∩ {ω : Ω | τ ω ≤ s}) := by
  intro s
  have h := (hτ s).diff (hA s)
  convert h using 1
  ext ω
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_compl_iff]
  tauto
