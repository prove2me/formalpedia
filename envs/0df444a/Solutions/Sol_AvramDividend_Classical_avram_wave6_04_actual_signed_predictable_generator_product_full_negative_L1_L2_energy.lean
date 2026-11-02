-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_generator_product_full_negative_L1_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:36:03.505641+00:00
-- url     : https://prove2.me/submissions/3a1a1d75-5793-476e-8381-817e93366e79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (a : (ℝ≥0 × Ω) → ℝ)
    (ha : Measurable[𝓕.rightCont.predictable] a)
    (haBound : ∀ p, |a p| ≤ (1 : ℝ))
    :
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
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    let GG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * JG p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GG p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GG p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by
  classical
  intro Y H HS GW JG GG
  have hEnergy :=
    avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha haBound
  have hPointwise (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      HS (p,z) = JG (p,z) := by
    have hk : H (p,z) =
        (if Y p ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0) :=
      avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ p z hz
    change
      (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) * H (p,z) =
      (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) *
        (if Y p ∈ Icc (u + δ) v then
          SpectrallyNegativeLevy.generatorIntegrand w (Y p) z else 0)
    rw [hk]
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hSet : MeasurableSet
      {p : ((ℝ≥0 × Ω) × ℝ) | p.2 < 0} :=
    (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ))).preimage measurable_snd
  have hNegative : ∀ᵐ p : ((ℝ≥0 × Ω) × ℝ)
      ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))), p.2 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae hSet).2
    filter_upwards [] with p
    exact ae_restrict_mem (μ := X.ν) measurableSet_Iio
  have hEqL1 :
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GG p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    apply lintegral_congr_ae
    filter_upwards [hNegative] with p hp
    change ENNReal.ofReal (|a p.1 * JG p|) =
      ENNReal.ofReal (|a p.1 * HS p|)
    rw [hPointwise p.1 p.2 hp]
  have hEqL2 :
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GG p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) =
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    apply lintegral_congr_ae
    filter_upwards [hNegative] with p hp
    change ENNReal.ofReal ((a p.1 * JG p) ^ 2) =
      ENNReal.ofReal ((a p.1 * HS p) ^ 2)
    rw [hPointwise p.1 p.2 hp]
  constructor
  · rw [hEqL1]
    exact hEnergy.1
  · rw [hEqL2]
    exact hEnergy.2