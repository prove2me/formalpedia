-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_generator_kernel_full_negative_mark_L2_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:49:39.764884+00:00
-- url     : https://prove2.me/submissions/499d3026-82be-4887-9c1e-39618af2443d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

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
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B)
      (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * JG (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by
  classical
  intro Y H HS JG B hBm hBneg hBanti hBempty
  have hTaylorL2 :=
    avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ a ha haBound B hBm hBneg hBanti hBempty
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
  have hEq (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * JG (p,z)) ^ 2) ∂X.ν ∂μ) =
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ) := by
    apply lintegral_congr
    intro p
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := X.ν) (hBm n)] with z hz
    rw [← hPointwise p z (hBneg n hz)]
  apply le_antisymm
  · calc
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * JG (p,z)) ^ 2) ∂X.ν ∂μ)
        ≤ (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ) := by
            apply iInf_mono
            intro n
            exact le_of_eq (hEq n)
      _ = 0 := hTaylorL2
  · exact bot_le