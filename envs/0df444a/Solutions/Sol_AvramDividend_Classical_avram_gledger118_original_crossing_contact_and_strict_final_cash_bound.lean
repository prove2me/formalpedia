-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger118_original_crossing_contact_and_strict_final_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T14:32:45.091491+00:00
-- url     : https://prove2.me/submissions/53d9b673-1399-462c-a28d-854e97856ed7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger84_original_strict_final_cell_cash_mono
import Theorems.Thm_AvramDividend_Classical_avram_gledger86_original_terminal_payment_cancel
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The final original crossing contact and strict cash are covered by the last strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (ρ δ a : ℝ≥0)
    (ha : (ρ : ℝ) - (δ : ℝ) ≤ (a : ℝ)) (hab : a ≤ ρ)
    (hDiv : rightLimit D a ω ≤ D ρ ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hfinite : (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)) ≠ ⊤) :
    Real.exp (-(q * (ρ : ℝ))) *
      ((w (x + X.X ρ ω - rightLimit D ρ ω) -
          w (x + X.X ρ ω - rightLimit D a ω)) +
        (w (riskProcess X x D ρ ω) -
          w (x + X.X ρ ω - rightLimit D ρ ω))) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal := by
  have hContact := avram_gledger86_original_terminal_payment_cancel
    X x D ω ρ a hDiv w C hTopCap hw0 hw_cont hw_neg hw_grad q
  have hCashENN := avram_gledger84_original_strict_final_cell_cash_mono
    X x D ω q ρ δ a ha hab
  have hCash := ENNReal.toReal_mono hfinite hCashENN
  linarith
