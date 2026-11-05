-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T20:10:43.080202+00:00
-- url     : https://prove2.me/submissions/54bd53e0-e16e-4a65-a4ac-cc4476950a01

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_stopped_signed_L1_of_named_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine closed-clock original diffuse Stieltjes component has an
integrable signed dividend-gradient remainder under a measurable selector. -/
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
        rightLimit D s.toNNReal ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hMeas : AEStronglyMeasurable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)) P) :
    Integrable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
            s.toNNReal - rightLimit D s.toNNReal ω)) ∂(μdiffuse ω)) P := by
  have hdom : ∀ ω, μdiffuse ω ≤ dividendMeasure D ω := by
    intro ω
    exact avram_p4_d_dividend_original_closed_stieltjes_diffuse_submeasure_actual_dividend
      D ω (τ ω) (μatom ω) (μdiffuse ω) (hsplit ω)
  exact avram_p4_d_dividend_original_random_stopped_signed_L1_of_named_cash
    X x D hD σ τ n hτ μdiffuse hdom q hq C w hwC2 a b hab hBand hstate
    Cash hCash hCashI hMeas
