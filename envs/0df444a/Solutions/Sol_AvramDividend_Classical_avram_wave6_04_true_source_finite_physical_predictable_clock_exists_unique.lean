-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_finite_physical_predictable_clock_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:53:35.511631+00:00
-- url     : https://prove2.me/submissions/df54f3b8-e23d-4df4-aab4-625b9b5acd58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∃! μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A =
          ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
            Real.toNNReal).prod P) A := by
  obtain ⟨μ, hfinite, hclock⟩ :=
    avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite (P := P) 𝓕 T
  refine ⟨μ, ⟨hfinite, hclock⟩, ?_⟩
  intro μ' hμ'
  exact avram_wave6_04_true_source_physical_predictable_clock_unique
    𝓕 T μ' μ hμ'.2 hclock
