-- Prove2me | solution 1 for AvramDividend.Classical.sampled_levy_filtration_exists_of_monotone_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:44:35.101775+00:00
-- url     : https://prove2.me/submissions/667b8794-958e-45d7-84b5-42400815d008

import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- Sample a continuous-time filtration at increasing times to use grid conditional expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s : ℕ → ℝ≥0) (hs : Monotone s) :
    ∃ 𝓖 : Filtration ℕ mΩ,
      (∀ k : ℕ, 𝓖 k = 𝓕 (s k)) ∧ SigmaFiniteFiltration P 𝓖 := by
  let 𝓖 : Filtration ℕ mΩ :=
    { seq := fun k => 𝓕 (s k)
      mono' := by
        intro i j hij
        exact 𝓕.mono (hs hij)
      le' := by
        intro i
        exact 𝓕.le (s i) }
  refine ⟨𝓖, ?_, inferInstance⟩
  intro k
  rfl
