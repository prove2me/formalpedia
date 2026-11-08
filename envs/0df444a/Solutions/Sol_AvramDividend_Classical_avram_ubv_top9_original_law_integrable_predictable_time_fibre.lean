-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_law_integrable_predictable_time_fibre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:28:57.473318+00:00
-- url     : https://prove2.me/submissions/2b6ffafe-85f7-4e2f-8903-516349a43847

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The source Lévy law is a probability measure, permitting Fubini for an
    integrable predictable integrand on the genuine physical-time clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (R : ℝ≥0 × Ω → ℝ)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμeq : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hR : Integrable R μ) :
    Integrable (fun ω : Ω =>
      ∫ t : ℝ≥0, R (t, ω) ∂
        (((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
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
    rw [hμeq A hA]
    exact (trim_measurableSet_eq hσ hA).symm
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  rw [heq] at hR
  have hProd : Integrable R μProd := integrable_of_integrable_trim hσ hR
  simpa [μProd] using hProd.integral_prod_right
