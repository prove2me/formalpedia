-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb62_sampled_original_rightCont_filtration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:36:43.261204+00:00
-- url     : https://prove2.me/submissions/2313b0f3-555c-424e-adfb-23b01dfbd779

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- Restrict the original continuous-time filtration to a deterministic mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (Δ : ℝ≥0) :
    ∃ (𝓖 : Filtration ℕ mΩ),
      ∀ i : ℕ, 𝓖 i = 𝓕.rightCont ((i : ℝ≥0) * Δ) := by
  let 𝓖 : Filtration ℕ mΩ := {
    seq := fun i => 𝓕.rightCont ((i : ℝ≥0) * Δ)
    mono' := by
      intro i j hij
      have hcast : (i : ℝ≥0) ≤ (j : ℝ≥0) := by
        exact_mod_cast hij
      exact (𝓕.rightCont).mono
        (mul_le_mul_of_nonneg_right hcast (by positivity))
    le' := by
      intro i
      exact (𝓕.rightCont).le _
  }
  exact ⟨𝓖, fun i => rfl⟩
