-- Prove2me | solution 1 for AvramDividend.Classical.stoppedHistory_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:32:11.865991+00:00
-- url     : https://prove2.me/submissions/c6ff739b-9f88-47ec-9076-3d1ab5ccba2d

import Mathlib.Probability.Process.Stopping

open MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    MeasurableSet A := by
  have e : A = ⋃ n : ℕ, A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
      exact ⟨n, h, hn⟩
    · rintro ⟨n, h, -⟩
      exact h
  rw [e]
  exact MeasurableSet.iUnion fun n => 𝓕.le _ _ (hA n)
