-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_BV_bounded_random_clock_signed_post_le_pre_expected
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:34:16.1432+00:00
-- url     : https://prove2.me/submissions/987d0db8-0824-4bc1-95fc-37d3dbe0fba4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original BV terminal L1 and expectation comparison at a physical
    bounded measurable random clock, preserving the strict ruin event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_meas : Measurable w)
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ) (hτBound : ∀ ω, τ ω ≤ H) :
    let Post : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0
    let Pre : Ω → ℝ := fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0
    Integrable Post P ∧ Integrable Pre P ∧
      (∫ ω, Post ω ∂P) ≤ (∫ ω, Pre ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  have hPost :
      Integrable (fun ω =>
        if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (τ ω : ℝ))) *
            w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
        else 0) P :=
    avram_p3_g2_original_bounded_random_clock_signed_postterminal_L1
      X hX hBV q hq w hw_cont hw0 hw_neg
      C hC hw_smooth hw_grad x hxc D hD H τ hτMeas hτBound
  have hPre :
      Integrable (fun ω =>
        if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * (τ ω : ℝ))) *
            w (riskProcess X x D (τ ω) ω)
        else 0) P :=
    avram_p3_g2_original_BV_bounded_random_clock_strict_prepayment_terminal_L1
      X hBV X.X_zero inferInstance x hx D hD.1.1 w hw_cont
      hw_meas q (le_of_lt hq) H τ hτMeas hτBound
  have hPoint : ∀ ω : Ω,
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) ≤
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0) :=
    avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment
      X C hC w hw_cont hw_smooth hw_grad x hxc D hD q τ
  exact ⟨hPost, hPre, integral_mono hPost hPre hPoint⟩
