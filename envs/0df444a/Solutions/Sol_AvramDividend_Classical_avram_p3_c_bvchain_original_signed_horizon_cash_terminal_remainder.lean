-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:52:34.139404+00:00
-- url     : https://prove2.me/submissions/c2a97bd0-fc9c-432d-8671-9f37871d5a70

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Physical closed cash plus strict-survival postpayment value is bounded by
strict cash plus prepayment value, including the inactive original ruin branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) (hS : 0 < S) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))
      else 0) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) := by
  by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hs]
    have hsplit := avram_p3_c_bvchain_original_literal_closed_cash_eq_strict_plus_horizon_atom
      X x C D hD ω q hq S
    have hatom := avram_wave8_21_original_active_horizon_rightpayment_discounted_hjump_budget
      X x D hD.1.1 w hjump ω S (Or.inr hs) q
    rw [hsplit]
    calc
      _ = (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          ((∫⁻ t in (paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ)) ∩
              ({(S : ℝ)} : Set ℝ),
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
            Real.exp (-(q * (S : ℝ))) *
              w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))) := by
          rw [add_assoc]
      _ ≤ _ := add_le_add_right hatom _
  · have hclock : ruinTime X x D ω ≤ ENNReal.ofReal (S : ℝ) := by
      have hle : ruinTime X x D ω ≤ (S : ℝ≥0∞) := le_of_not_gt hs
      simpa using hle
    have hSreal : (0 : ℝ) < (S : ℝ) := by exact_mod_cast hS
    have hruin := avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
      X x D ω q (S : ℝ) hSreal hclock
    simpa only [if_neg hs, add_zero] using le_of_eq hruin
