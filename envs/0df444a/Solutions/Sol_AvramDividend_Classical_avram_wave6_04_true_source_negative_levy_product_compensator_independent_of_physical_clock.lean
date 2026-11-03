-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_compensator_independent_of_physical_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:45:15.651194+00:00
-- url     : https://prove2.me/submissions/933f628f-7d0c-48dd-98a0-628b0457b838

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true source negative Lévy product compensator is independent of
the presentation of the canonical finite-horizon physical predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     μ₁.prod (X.ν.restrict (Iio (0 : ℝ)))) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     μ₂.prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  have hμ : μ₁ = μ₂ :=
    avram_wave6_04_true_source_physical_predictable_clock_unique
      𝓕 T μ₁ μ₂ hμ₁ hμ₂
  rw [hμ]
