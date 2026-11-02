-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_C2_jump_generator_full_negative_energy_tail_interface
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:32:20.728642+00:00
-- url     : https://prove2.me/submissions/37455c28-b203-4d31-b466-310f4e200350

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_weight_generator_negative_mark_L1_tail

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
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal ((GW p) ^ 2)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|a p * HS (p,z)|) ∂X.ν ∂μ) = 0 ∧
    (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖a p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by
  classical
  intro Y H HS GW JG
  have hEnergy :=
    avram_wave6_04_actual_predictable_contraction_source_product_L1_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha haBound
  have hTaylorL1 :=
    avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha haBound B hBm hBneg hBanti hBempty
  have hTaylorL2 :=
    avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha haBound B hBm hBneg hBanti hBempty
  have hGenerator :=
    avram_wave6_04_actual_signed_predictable_weight_generator_negative_mark_L1_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      T B hBm hBneg hBanti hBempty a ha haBound
  exact ⟨hEnergy.1, hEnergy.2, hTaylorL1, hTaylorL2, hGenerator⟩