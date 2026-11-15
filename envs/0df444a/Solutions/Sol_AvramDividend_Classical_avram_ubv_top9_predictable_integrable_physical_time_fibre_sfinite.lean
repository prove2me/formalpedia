-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_predictable_integrable_physical_time_fibre_sfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:56:01.20671+00:00
-- url     : https://prove2.me/submissions/23ad00c2-62f0-4c6b-8094-2460542f8239

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
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
