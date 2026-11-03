-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_future_rectangle_compensator_clock_representation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:47:13.57257+00:00
-- url     : https://prove2.me/submissions/5b55d122-e817-4799-bb5f-b21babe12bf7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source-specific future jump-rectangle compensator transport does not
depend on which representation of the physical predictable clock is used. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
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
          Real.toNNReal).prod P) A)
    (hFuture₁ : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         (μ₁.prod (X.ν.restrict (Iio (0 : ℝ))))
            ((Set.Ioi i ×ˢ A) ×ˢ C))) :
    ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         (μ₂.prod (X.ν.restrict (Iio (0 : ℝ))))
            ((Set.Ioi i ×ˢ A) ×ˢ C)) := by
  have hμ : μ₁ = μ₂ :=
    avram_wave6_04_true_source_physical_predictable_clock_unique
      𝓕 T μ₁ μ₂ hμ₁ hμ₂
  subst μ₂
  exact hFuture₁
