-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_21_original_strict_survival_discounted_full_cash_le_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:49:58.340761+00:00
-- url     : https://prove2.me/submissions/ba4671ad-6b1d-49a7-9e9c-fe2277a437ab

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact original strict pre-ruin cash is bounded by its closed-horizon total Stieltjes budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (ω : Ω) (T : ℝ≥0)
    (hstrict : (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (rightLimit D T ω) := by
  rw [avram_wave8_21_original_paymentTimes_strict_horizon_eq_Icc
    (ruinTime X x D ω) T hstrict]
  exact avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
    q hq D hD ω T
