-- Prove2me | solution 1 for AvramDividend.Classical.avram_f21_original_earlier_clock_terminal_L1_from_exact_payoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:33:28.245149+00:00
-- url     : https://prove2.me/submissions/b8d92c80-9a66-4891-8fd5-39ec17e40457

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_ordered_clocks_closed_cash_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ τ : Ω → ℝ≥0) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσmeas : Measurable (fun ω => (σ ω : ℝ)))
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (Term F : Ω → ℝ)
    (hF : ∀ ω, F ω = Term ω +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    Integrable Term P := by
  have hCashσI :=
    avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
      X x q hq C D hD σ τ hστ hσmeas hCashτI
  have hEq : Term = (fun ω => F ω -
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) := by
    funext ω
    rw [hF ω]
    ring
  rw [hEq]
  exact hFI.sub hCashσI
