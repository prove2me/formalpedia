-- Prove2me | solution 1 for AvramDividend.Classical.stoppedEvent_upperGridFibre_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:11:00.551987+00:00
-- url     : https://prove2.me/submissions/8aa5c991-94b9-4ee9-9e21-b2d9ec011fdb

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0) :
    MeasurableSet[𝓕 s]
      (A ∩ {ω : Ω | τn n ω = s}) := by
  have e : A ∩ {ω : Ω | τn n ω = s} = (A ∩ {ω : Ω | τ ω ≤ s}) ∩ {ω : Ω | τn n ω = s} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ha, hs⟩
      exact ⟨⟨ha, hs ▸ habove ω n⟩, hs⟩
    · rintro ⟨⟨ha, -⟩, hs⟩
      exact ⟨ha, hs⟩
  rw [e]
  exact (hA s).inter (hfibres n s)
