-- Prove2me | solution 1 for AvramDividend.Classical.expected_capped_gradient_payment_weighted_interior_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:47:42.12993+00:00
-- url     : https://prove2.me/submissions/0b9db3f3-bbe3-4b68-80a5-a8f3a5e4da0b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_capped_gradient_discounted_payment_weighted_interior_boundary
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Integrate the gradient-only stopped Stieltjes payout inequality over all scenarios. The boundary mass is retained exactly, with no absolute-continuity or countable-jump assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (σ : Ω → ℝ≥0∞) (T : ℝ≥0) (u : Ω → ℝ → ℝ)
    (hInterior : ∀ ω, MeasurableSet
      {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C}) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω,
      (∫⁻ t in (paymentTimes (σ ω) ∩ Iic (T : ℝ)) ∩
        {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
        ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u ω t))
          ∂(dividendMeasure D ω)) +
      (∫⁻ t in (paymentTimes (σ ω) ∩ Iic (T : ℝ)) \
        {t : ℝ | 0 < u ω t ∧ ENNReal.ofReal (u ω t) < C},
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ∂P) := by
  apply MeasureTheory.lintegral_mono
  intro ω
  exact capped_gradient_discounted_payment_weighted_interior_boundary
    X D hD q w C hw_grad (σ ω) T ω (u ω) (hInterior ω)
