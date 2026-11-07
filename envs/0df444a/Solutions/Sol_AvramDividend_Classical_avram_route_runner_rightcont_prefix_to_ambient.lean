-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_rightcont_prefix_to_ambient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:08:12.27898+00:00
-- url     : https://prove2.me/submissions/4c3abe30-8c4d-40cd-88fa-78ba4ea4981e

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- A filtration event belongs to the ambient sample-space sigma algebra. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (u : ℕ → ℝ≥0) (k : Ω → ℕ)
    (hPredictable : ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω}) :
    ∀ i, MeasurableSet {ω : Ω | i < k ω} := by
  intro i
  have hle : (𝓕.rightCont (u i) : MeasurableSpace Ω) ≤ mΩ :=
    (𝓕.rightCont).le (u i)
  exact hle _ (hPredictable i)
