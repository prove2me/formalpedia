-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_true_Levy_finite_predictable_physical_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:11:04.223882+00:00
-- url     : https://prove2.me/submissions/b15cc4dc-c2be-48ba-852e-f26673b4785f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨μ, hμ, _⟩ :=
    avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
      (P := P) 𝓕 T
  exact ⟨μ, hμ⟩

