-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:09:12.232589+00:00
-- url     : https://prove2.me/submissions/21570bc6-579a-4642-9c39-20eb99b3a3a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
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
    (haBound : ∀ p, |a p| ≤ (1 : ℝ)) :
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by
  classical
  intro Y H HS GW
  have hL1 :
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
          ENNReal.ofReal (|HS p|)
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) :=
    avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hL2 :
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
          ENNReal.ofReal ((HS p) ^ 2)
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) :=
    avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  constructor
  · calc
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
          ENNReal.ofReal (|GW p|)
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
        ≤ (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
            ENNReal.ofReal (|HS p|)
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
            apply lintegral_mono
            intro p
            apply ENNReal.ofReal_le_ofReal
            change |a p.1 * HS p| ≤ |HS p|
            calc
              |a p.1 * HS p| = |a p.1| * |HS p| := abs_mul _ _
              _ ≤ 1 * |HS p| :=
                mul_le_mul_of_nonneg_right (haBound p.1) (abs_nonneg _)
              _ = |HS p| := one_mul _
      _ < ⊤ := hL1
  · calc
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
          ENNReal.ofReal ((GW p) ^ 2)
          ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
        ≤ (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          ∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
            ENNReal.ofReal ((HS p) ^ 2)
            ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
            apply lintegral_mono
            intro p
            apply ENNReal.ofReal_le_ofReal
            change (a p.1 * HS p) ^ 2 ≤ (HS p) ^ 2
            have hab : |a p.1| ≤ (1 : ℝ) := haBound p.1
            have haLo : -1 ≤ a p.1 := (abs_le.mp hab).1
            have haHi : a p.1 ≤ 1 := (abs_le.mp hab).2
            have hp : 0 ≤ (1 - a p.1) * (1 + a p.1) :=
              mul_nonneg (sub_nonneg.mpr haHi) (by linarith)
            have haSq : (a p.1) ^ 2 ≤ 1 := by nlinarith
            calc
              (a p.1 * HS p) ^ 2 =
                  (a p.1) ^ 2 * (HS p) ^ 2 := by ring
              _ ≤ 1 * (HS p) ^ 2 :=
                mul_le_mul_of_nonneg_right haSq (sq_nonneg _)
              _ = (HS p) ^ 2 := one_mul _
      _ < ⊤ := hL2

