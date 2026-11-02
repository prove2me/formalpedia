-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_source_product_generator_drift_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:59:19.099395+00:00
-- url     : https://prove2.me/submissions/1da52b8c-7ced-463c-baf4-f978282ca04e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every bounded predictable discount of the actual stopped nonlinear source
jump kernel has a genuine original X.ν product-integral generator drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (M : ℝ) (haBound : ∀ p, |a p| ≤ M) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     Integrable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * HS p)
       (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
     (∫ p : ((ℝ≥0 × Ω) × ℝ), a p.1 * HS p
       ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
       ∫ p : ℝ≥0 × Ω,
         a p * (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) ∂μ) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hbase :=
    (avram_wave5_03b_actual_source_product_compensator_generator_drift_eq
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ).1
  have hInt : Integrable HS (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := hbase
  have haMarked : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1) :=
    ha.comp measurable_fst
  have hBound : ∀ᵐ p : ((ℝ≥0 × Ω) × ℝ)
      ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))), ‖a p.1‖ ≤ M :=
    Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using haBound p.1)
  have hIntW : Integrable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * HS p)
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) :=
    hInt.bdd_mul haMarked.aestronglyMeasurable hBound
  have hSection (p : ℝ≥0 × Ω) :
      (∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
    simpa [HS, H, JG, Y] using
      (avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
        X x D hD w u v δ p (Iio (0 : ℝ))
        measurableSet_Iio (Subset.rfl))
  change Integrable (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * HS p)
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) ∧
      (∫ p : ((ℝ≥0 × Ω) × ℝ), a p.1 * HS p
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
      ∫ p : ℝ≥0 × Ω, a p *
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) ∂μ
  refine ⟨hIntW, ?_⟩
  rw [MeasureTheory.integral_prod _ hIntW]
  apply integral_congr_ae
  filter_upwards with p
  calc
    (∫ z : ℝ, a p * HS (p,z) ∂(X.ν.restrict (Iio (0 : ℝ)))) =
        a p * (∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) := by
      rw [integral_const_mul]
    _ = a p * (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) :=
      congrArg (fun r : ℝ => a p * r) (hSection p)
