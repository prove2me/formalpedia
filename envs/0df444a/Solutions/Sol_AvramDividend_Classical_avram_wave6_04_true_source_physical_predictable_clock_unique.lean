-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_physical_predictable_clock_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:22:47.476205+00:00
-- url     : https://prove2.me/submissions/2dcbe63d-e4d2-418f-8421-61ceb34d7a7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ₁ μ₂ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ₁ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₁ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hμ₂ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₂ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) :
    μ₁ = μ₂ := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  apply Measure.ext
  intro A hA
  exact (hμ₁ A hA).trans (hμ₂ A hA).symm
