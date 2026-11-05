-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_jointly_measurable_stopped_diffuse_L1_of_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:05:53.617449+00:00
-- url     : https://prove2.me/submissions/ecd09694-9393-4e5d-8a3b-82bde49fc89b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A jointly measurable actual stopped dividend-gradient integrand yields
L¹ of the original discounted signed diffuse Stieltjes remainder from the
exact named Cash integrability witness, with no independent integral-selector
measurability premise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (n : ℕ)
    (hτ : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (μatom : Ω → Measure ℝ) (κdiff : Kernel Ω ℝ)
    [IsSFiniteKernel κdiff]
    (hsplit : ∀ ω,
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)) =
        μatom ω + κdiff ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hstate : ∀ ω, ∀ᵐ s ∂(κdiff ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (σ ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hWindow : ∀ ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)))
    (hJoint : StronglyMeasurable (fun p : Ω × ℝ =>
      (paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)).indicator
        (fun s : ℝ => Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r p.1) s.toNNReal -
            rightLimit D s.toNNReal p.1))) p.2)) :
    Integrable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) P := by
  have hMeas : AEStronglyMeasurable (fun ω =>
      ∫ s in (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
        Real.exp (-(q * s)) *
          (1 - deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω)) ∂κdiff ω) P :=
    (avram_p4_d_dividend_original_stopped_diffuse_signed_kernel_integral_measurable
      X x D hD σ τ q w κdiff hWindow hJoint).aestronglyMeasurable
  exact avram_p4_d_dividend_original_actual_diffuse_stieltjes_random_stopped_L1_of_named_cash
    X x D hD σ τ n hτ μatom (fun ω => κdiff ω) hsplit
    q hq C w hwC2 a b hab hBand hstate Cash hCash hCashI hMeas
