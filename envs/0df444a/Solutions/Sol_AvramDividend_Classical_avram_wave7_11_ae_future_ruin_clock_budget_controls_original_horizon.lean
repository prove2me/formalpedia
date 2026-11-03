-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_ae_future_ruin_clock_budget_controls_original_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:08:18.709801+00:00
-- url     : https://prove2.me/submissions/a9e3ad31-c89a-4b59-b0e8-862366f88357

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_strict_future_clock_preserves_finite_payment_set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One almost-surely future stopped cash budget controls the exact
    original finite-horizon Stieltjes value, including its right endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (η : Ω → ℝ≥0∞)
    (hFuture : ∀ᵐ ω ∂P, ENNReal.ofReal T < η ω)
    (b : ℝ≥0∞)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ b := by
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (min (ruinTime X x D ω) (η ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
          apply lintegral_congr_ae
          filter_upwards [hFuture] with ω hω
          rw [avram_wave7_11_strict_future_clock_preserves_finite_payment_set
            (ruinTime X x D ω) (η ω) T hω]
    _ ≤ b := hBudget
