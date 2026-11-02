-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_signed_predictable_contraction_taylor_negative_mark_L2_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:27:36.170616+00:00
-- url     : https://prove2.me/submissions/23e272eb-e3af-4ee2-877e-4de9d1c38f71

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail

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
        ∫⁻ z in B n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by
  classical
  intro Y H HS B hBm hBneg hBanti hBempty
  have hBase :
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 := by
    exact
      avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
        X x D hD w (0 : ℝ) C u v δ hw hw_cont hw_neg
        hu (by linarith [huv, hδ]) hv (le_of_lt hu) hδ hδone
        (le_of_lt huv) μ hμ B hBm hBneg hBanti hBempty
  apply le_antisymm
  · calc
      (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((a p * HS (p,z)) ^ 2) ∂X.ν ∂μ)
        ≤ (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) := by
            apply iInf_mono
            intro n
            apply lintegral_mono
            intro p
            apply lintegral_mono
            intro z
            apply ENNReal.ofReal_le_ofReal
            have hab : |a p| ≤ (1 : ℝ) := haBound p
            have haLo : -1 ≤ a p := (abs_le.mp hab).1
            have haHi : a p ≤ 1 := (abs_le.mp hab).2
            have hp : 0 ≤ (1 - a p) * (1 + a p) :=
              mul_nonneg (sub_nonneg.mpr haHi) (by linarith)
            have haSq : (a p) ^ 2 ≤ 1 := by nlinarith
            calc
              (a p * HS (p,z)) ^ 2 =
                  (a p) ^ 2 * (HS (p,z)) ^ 2 := by ring
              _ ≤ 1 * (HS (p,z)) ^ 2 :=
                mul_le_mul_of_nonneg_right haSq (sq_nonneg _)
              _ = (HS (p,z)) ^ 2 := one_mul _
      _ = 0 := hBase
  · exact bot_le
