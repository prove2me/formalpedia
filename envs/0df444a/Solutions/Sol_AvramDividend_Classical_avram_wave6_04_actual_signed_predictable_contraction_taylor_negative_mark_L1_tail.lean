-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L1_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:13:33.335262+00:00
-- url     : https://prove2.me/submissions/5f6113e0-2411-4b2d-a544-232c29a70a4e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail

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
    ∀ (B : ℕ → Set ℝ)
      (hBm : ∀ n, MeasurableSet (B n))
      (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
      (hBanti : Antitone B)
      (hBempty : (⋂ n, B n) = ∅),
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|a p * HS (p,z)|) ∂X.ν ∂μ) = 0 := by
  classical
  intro Y H HS B hBm hBneg hBanti hBempty
  have hBase :
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ B hBm hBneg hBanti hBempty
  apply le_antisymm
  · calc
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|a p * HS (p,z)|) ∂X.ν ∂μ)
        ≤ (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) := by
            apply iInf_mono
            intro n
            apply lintegral_mono
            intro p
            apply lintegral_mono
            intro z
            apply ENNReal.ofReal_le_ofReal
            calc
              |a p * HS (p,z)| = |a p| * |HS (p,z)| := abs_mul _ _
              _ ≤ 1 * |HS (p,z)| :=
                mul_le_mul_of_nonneg_right (haBound p) (abs_nonneg _)
              _ = |HS (p,z)| := one_mul _
      _ = 0 := hBase
  · exact bot_le
