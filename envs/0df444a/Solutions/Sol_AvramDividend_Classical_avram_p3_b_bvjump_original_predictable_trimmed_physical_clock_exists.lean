-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:11:09.656297+00:00
-- url     : https://prove2.me/submissions/27a5fc91-abef-4c71-afcf-4e229a40ee77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Construct the genuine original predictable time-path intensity clock by
trimming the physical mapped-Lebesgue times probability product measure. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ∞ ∧
      ∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A := by
  let clock := ((volume : Measure ℝ).restrict
    (Icc 0 (T : ℝ))).map Real.toNNReal
  let hm : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    avram_p3_b_bvjump_original_predictable_le_product_space 𝓕
  let μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable) :=
    (clock.prod P).trim hm
  have hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = (clock.prod P) A := by
    intro A hA
    exact trim_measurableSet_eq hm hA
  exact ⟨μ,
    avram_p3_b_bvjump_original_predictable_physical_clock_mass_finite
      T μ hμclock,
    hμclock⟩
