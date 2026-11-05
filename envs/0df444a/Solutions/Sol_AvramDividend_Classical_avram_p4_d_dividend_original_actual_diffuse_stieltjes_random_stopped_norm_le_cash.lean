-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_norm_le_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:09:37.622841+00:00
-- url     : https://prove2.me/submissions/63454309-b087-4352-aa7c-ad0f1233d277

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An actual original closed-clock atomic/diffuse Stieltjes decomposition
automatically supplies domination for the uniform diffuse signed-Cash bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (μatom μdiffuse : Ω → Measure ℝ)
    (hsplit : ∀ ω,
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)) =
        μatom ω + μdiffuse ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(μdiffuse ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ω,
      ‖∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)‖ ≤
        (1 + K) * Real.exp (q * (n : ℝ)) *
          (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hdom : ∀ ω, μdiffuse ω ≤ dividendMeasure D ω := by
    intro ω
    exact avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
      D ω (τ ω) (μatom ω) (μdiffuse ω) (hsplit ω)
  exact avram_p4_d_dividend_original_random_stopped_signed_norm_le_uniform_cash
    X x D hD σ τ n hτ μdiffuse hdom q hq C w hwC2 a b hab hBand hstate
