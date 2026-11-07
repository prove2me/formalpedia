-- Prove2me | solution 1 for AvramDividend.Classical.avram_sweep16_20261106_natural_closed_budgets_imply_full_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:46:31.810195+00:00
-- url     : https://prove2.me/submissions/69c64102-29f3-4811-b893-88e65fa2b98d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
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
    (hNatural : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (((min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by
  apply avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon X x q T D budget
  intro n hn
  have hSetCash := avram_sweep16_20261106_strict_clipped_cash_le_natural_closed
    P (fun ω => ruinTime X x D ω) (dividendMeasure D)
    (fun _ t => ENNReal.ofReal (Real.exp (-(q * t)))) n T
  exact hSetCash.trans (hNatural n hn)
