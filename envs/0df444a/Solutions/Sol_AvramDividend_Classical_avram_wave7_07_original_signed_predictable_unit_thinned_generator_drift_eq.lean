-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_signed_predictable_unit_thinned_generator_drift_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:04:40.644204+00:00
-- url     : https://prove2.me/submissions/dd3caf69-006e-4997-b3a5-20df65a2a161

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any predictable signed unit contraction preserves the exact original
stopped C² negative-jump generator drift identity and L1 integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, |a p| ≤ 1) :
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      a p * (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν)) μ ∧
    (∫ p : ℝ≥0 × Ω,
      a p * (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∂μ) =
    (∫ p : ℝ≥0 × Ω,
      a p * (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) ∂μ) := by
  classical
  intro Y H HS G
  have hBase :=
    avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ S hS
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hBound : ∀ᵐ p : ℝ≥0 × Ω ∂μ, ‖a p‖ ≤ (1 : ℝ) := by
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using ha p
  have hInt : Integrable (fun p : ℝ≥0 × Ω =>
      a p * (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν)) μ :=
    hBase.1.bdd_mul ham.aestronglyMeasurable hBound
  refine ⟨hInt, ?_⟩
  have hFunEq :
      (fun p : ℝ≥0 × Ω =>
        a p * (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν)) =
      (fun p : ℝ≥0 × Ω =>
        a p * (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν)) := by
    funext p
    rw [hBase.2 p]
  exact congrArg (fun f : (ℝ≥0 × Ω) → ℝ => ∫ p, f p ∂μ) hFunEq
