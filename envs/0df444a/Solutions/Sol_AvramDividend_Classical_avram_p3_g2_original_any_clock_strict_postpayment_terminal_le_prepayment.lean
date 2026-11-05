-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g2_original_any_clock_strict_postpayment_terminal_le_prepayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:24:41.566948+00:00
-- url     : https://prove2.me/submissions/213d76c9-6c1d-4c65-a002-4484a75c7720

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-payment terminal never exceeds the prepayment
    terminal at any physical observation clock, including random clocks,
    zero, and cap contact; the ruin tie has both terminals zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)
      else 0) ≤
      (if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (τ ω : ℝ))) *
          w (riskProcess X x D (τ ω) ω)
      else 0) := by
  intro ω
  by_cases hs : (τ ω : ℝ≥0∞) < ruinTime X x D ω
  · have hΔ : 0 ≤ rightLimit D (τ ω) ω - D (τ ω) ω :=
      sub_nonneg.mpr
        (dividendStrategy_le_rightLimit D hD.1.1 ω (τ ω))
    have hJump :=
      avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
        X C hC w hw_cont hw_smooth hw_grad x hxc D hD
        ω (τ ω) (Or.inr hs)
    have hIdentity :
        riskProcess X x D (τ ω) ω -
          (rightLimit D (τ ω) ω - D (τ ω) ω) =
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω := by
      unfold riskProcess
      ring
    rw [hIdentity] at hJump
    have hPrePost :
        w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) ≤
          w (riskProcess X x D (τ ω) ω) := by
      linarith only [hΔ, hJump]
    simp only [hs, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left hPrePost
      (le_of_lt (Real.exp_pos _))
  · simp [hs]
