-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_ae_predictable_integral_equals_physical_time_probability_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:15:57.855034+00:00
-- url     : https://prove2.me/submissions/4fe06ff2-ae11-4502-be99-2d37dc0bd133


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On any almost-everywhere source right-continuous predictable integrand,
the canonical source physical-time clock integral is precisely the
ordinary finite-horizon real-time × P product integral. This says
nothing about the stochastic jump-count intensity, still Chat01. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (f : (ℝ≥0 × Ω) → ℝ)
    (hf : AEStronglyMeasurable[𝓕.rightCont.predictable] f μ) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω, f p ∂μ) =
      ∫ p : ℝ≥0 × Ω, f p
        ∂((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) := by
  classical
  have hσ : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) := by
    apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      have hA0 : MeasurableSet A := (𝓕.rightCont.le ⊥) A hA
      exact (measurableSet_singleton (0 : ℝ≥0)).prod hA0
    · intro i A hA
      have hA0 : MeasurableSet A := (𝓕.rightCont.le i) A hA
      exact measurableSet_Ioi.prod hA0
  let μProd : Measure (ℝ≥0 × Ω) :=
    ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P)
  have heq : μ = μProd.trim hσ := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply Measure.ext
    intro A hA
    rw [hμclock A hA]
    exact (trim_measurableSet_eq hσ hA).symm
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  rw [heq] at hf ⊢
  exact (integral_trim_ae hσ hf).symm