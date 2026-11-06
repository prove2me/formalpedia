-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:38:00.69422+00:00
-- url     : https://prove2.me/submissions/db5c1af0-aecb-4c2f-9c99-086ef5a87c16

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
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
    (hEach : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max T (0 : ℝ))
  have hnRealPos : (0 : ℝ) < (n : ℝ) :=
    lt_of_le_of_lt (le_max_right T 0) hn
  have hnPos : 0 < n := by exact_mod_cast hnRealPos
  have hTn : T < (n : ℝ) :=
    lt_of_le_of_lt (le_max_left T 0) hn
  rw [← avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
    X x D q T n hnPos hTn]
  exact hEach n hnPos
