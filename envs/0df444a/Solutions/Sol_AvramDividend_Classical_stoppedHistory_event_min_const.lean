-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_event_min_const
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:07:38.252588+00:00
-- url     : https://prove2.me/submissions/ca30b14b-84fd-4fc0-8296-b3746f17d07f

import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal

/-- A stopped-history event truncated at a horizon remains a stopped-history event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (T s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      ((A ∩ {ω : Ω | τ ω ≤ T}) ∩
        {ω : Ω | min (τ ω) T ≤ s}) := by
  by_cases hTs : T ≤ s
  · have heq :
        (A ∩ {ω : Ω | τ ω ≤ T}) ∩
            {ω : Ω | min (τ ω) T ≤ s} =
          A ∩ {ω : Ω | τ ω ≤ T} := by
      ext ω
      constructor
      · exact And.left
      · intro hω
        exact ⟨hω, le_trans (min_le_right (τ ω) T) hTs⟩
    rw [heq]
    exact 𝓕.mono hTs _ (hA T)
  · have hsT : s < T := lt_of_not_ge hTs
    have heq :
        (A ∩ {ω : Ω | τ ω ≤ T}) ∩
            {ω : Ω | min (τ ω) T ≤ s} =
          A ∩ {ω : Ω | τ ω ≤ s} := by
      ext ω
      constructor
      · rintro ⟨⟨hωA, hωT⟩, hmin⟩
        change min (τ ω) T ≤ s at hmin
        rcases (min_le_iff.mp hmin) with hωs | hT'
        · exact ⟨hωA, hωs⟩
        · exact False.elim (hTs hT')
      · rintro ⟨hωA, hωs⟩
        exact ⟨⟨hωA, le_trans hωs (le_of_lt hsT)⟩,
          le_trans (min_le_left (τ ω) T) hωs⟩
    rw [heq]
    exact hA s
