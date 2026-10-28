-- Prove2me | solution 1 for AvramDividend.Classical.exists_nat_filtration_along_monotone_nonnegative_time_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:19:57.601533+00:00
-- url     : https://prove2.me/submissions/79f36690-6e0f-4d40-bf70-8bada5b02494

import Mathlib.Probability.Process.Filtration
open MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (g : ℕ → ℝ≥0) (hg : Monotone g) :
    ∃ 𝓖 : Filtration ℕ mΩ, ∀ n : ℕ, 𝓖 n = 𝓕 (g n) :=
  ⟨⟨fun n => 𝓕 (g n), fun _ _ h => 𝓕.mono (hg h), fun n => 𝓕.le (g n)⟩, fun _ => rfl⟩
