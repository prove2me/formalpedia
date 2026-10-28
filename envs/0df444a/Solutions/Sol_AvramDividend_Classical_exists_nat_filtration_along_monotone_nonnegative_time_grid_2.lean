-- Prove2me | solution 2 for AvramDividend.Classical.exists_nat_filtration_along_monotone_nonnegative_time_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:20:16.748169+00:00
-- url     : https://prove2.me/submissions/6e37d4be-af7f-4a3a-9dc5-64a162def713

import Mathlib.Probability.Process.Filtration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (g : ℕ → ℝ≥0) (hg : Monotone g) :
    ∃ 𝓖 : Filtration ℕ mΩ, ∀ n : ℕ, 𝓖 n = 𝓕 (g n) := by
  refine ⟨⟨(fun n => 𝓕 (g n)), ?_, ?_⟩, ?_⟩
  · intro i j hij
    exact 𝓕.mono (hg hij)
  · intro i
    exact 𝓕.le (g i)
  · intro n
    rfl
