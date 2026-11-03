-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_generic_bv_stieltjes_Ioc_product_of_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:28:06.609902+00:00
-- url     : https://prove2.me/submissions/be33425a-0889-447d-86f4-3a093647ad36

import Mathlib
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

noncomputable section

/-- BV Stieltjes integration by parts on a half-open interval reduces to
the exact Fubini exchange of its two cumulative increments. -/
theorem solution
    (f g : ℝ≥0 → ℝ)
    (hf : BoundedVariationOn f Set.univ)
    (hg : BoundedVariationOn g Set.univ)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hFubini :
      (∫ᵛ t in Ioc a b, (Function.rightLim g t - Function.rightLim g a) ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b, (Function.rightLim f b - Function.leftLim f t) ∂• hg.vectorMeasure)) :
    (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) =
      Function.rightLim f b • Function.rightLim g b -
      Function.rightLim f a • Function.rightLim g a -
      (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) := by
  obtain ⟨hfl, _, hgr, _⟩ :=
    avram_wave6_05_generic_bv_vector_stieltjes_interval_integrability f g hf hg a b hab
  have hfinite (μ : VectorMeasure ℝ≥0 ℝ) : IsFiniteMeasure μ.variation := by
    rw [← SignedMeasure.totalVariation_eq_variation]
    infer_instance
  letI : IsFiniteMeasure hf.vectorMeasure.variation := hfinite hf.vectorMeasure
  letI : IsFiniteMeasure hg.vectorMeasure.variation := hfinite hg.vectorMeasure
  haveI : IsFiniteMeasure (hf.vectorMeasure.restrict (Ioc a b)).variation :=
    inferInstance
  haveI : IsFiniteMeasure (hg.vectorMeasure.restrict (Ioc a b)).variation :=
    inferInstance
  have hconstg : (hf.vectorMeasure.restrict (Ioc a b)).Integrable
      (fun _ : ℝ≥0 => Function.rightLim g a) := by
    change Integrable (fun _ : ℝ≥0 => Function.rightLim g a)
      ((hf.vectorMeasure.restrict (Ioc a b)).variation)
    exact integrable_const _
  have hconstf : (hg.vectorMeasure.restrict (Ioc a b)).Integrable
      (fun _ : ℝ≥0 => Function.rightLim f b) := by
    change Integrable (fun _ : ℝ≥0 => Function.rightLim f b)
      ((hg.vectorMeasure.restrict (Ioc a b)).variation)
    exact integrable_const _
  have hLeft :
      (∫ᵛ t in Ioc a b, Function.rightLim g t - Function.rightLim g a
        ∂<• hf.vectorMeasure) =
      (∫ᵛ t in Ioc a b, Function.rightLim g t ∂<• hf.vectorMeasure) -
        Function.rightLim g a • hf.vectorMeasure (Ioc a b) := by
    rw [VectorMeasure.integral_fun_sub hgr hconstg, VectorMeasure.setIntegral_const]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply]
    ring
  have hRight :
      (∫ᵛ t in Ioc a b, Function.rightLim f b - Function.leftLim f t
        ∂• hg.vectorMeasure) =
      Function.rightLim f b • hg.vectorMeasure (Ioc a b) -
        (∫ᵛ t in Ioc a b, Function.leftLim f t ∂• hg.vectorMeasure) := by
    rw [VectorMeasure.integral_fun_sub hconstf hfl, VectorMeasure.setIntegral_const]
    simp only [ContinuousLinearMap.lsmul_apply]
  rw [hLeft, hRight, hf.vectorMeasure_Ioc hab, hg.vectorMeasure_Ioc hab] at hFubini
  simp only [smul_eq_mul] at hFubini ⊢
  linear_combination hFubini
