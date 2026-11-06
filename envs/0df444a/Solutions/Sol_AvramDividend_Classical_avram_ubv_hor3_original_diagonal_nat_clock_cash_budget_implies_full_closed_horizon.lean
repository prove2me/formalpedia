-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_diagonal_nat_clock_cash_budget_implies_full_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:03:43.487819+00:00
-- url     : https://prove2.me/submissions/375a4748-5dab-4e49-8743-9650cbef9fe6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (budget : ℝ≥0∞)
    (hClock : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by
  apply avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon X x q T D budget
  intro n hn
  exact (avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
    X x D q T n hn).trans (hClock n hn)
