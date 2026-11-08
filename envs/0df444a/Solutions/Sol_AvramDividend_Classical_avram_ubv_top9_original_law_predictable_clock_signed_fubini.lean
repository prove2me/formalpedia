-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_law_predictable_clock_signed_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:52:04.770826+00:00
-- url     : https://prove2.me/submissions/9fad8bdc-1fce-4859-97fe-1495ac324127

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Signed Fubini on the original finite predictable physical clock. -/
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
    (∫ ω : Ω, ∫ t : ℝ≥0, R (t, ω) ∂
      (((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal) ∂P) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω, R p ∂μ) := by
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
  let mT : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  let μProd : Measure (ℝ≥0 × Ω) := mT.prod P
  have heq : μ = μProd.trim hσ := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    apply Measure.ext
    intro A hA
    rw [hμeq A hA]
    exact (trim_measurableSet_eq hσ hA).symm
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  rw [heq] at hR ⊢
  have hProd : Integrable R μProd := integrable_of_integrable_trim hσ hR
  have hSwap := integral_integral_swap (f := fun t ω => R (t, ω)) hProd
  have hProdEq := integral_prod R hProd
  calc
    (∫ ω : Ω, ∫ t : ℝ≥0, R (t, ω) ∂mT ∂P) =
        ∫ t : ℝ≥0, ∫ ω : Ω, R (t, ω) ∂P ∂mT := hSwap.symm
    _ = ∫ p : ℝ≥0 × Ω, R p ∂μProd := hProdEq.symm
    _ = ∫ p : ℝ≥0 × Ω, R p ∂μProd.trim hσ :=
      integral_trim_ae hσ hR.aestronglyMeasurable
