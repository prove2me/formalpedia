-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_canonical_signed_horizon_correction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:04:50.373194+00:00
-- url     : https://prove2.me/submissions/97903dfc-632e-4a04-bf14-71f3eb1b51e1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_strict_survival_terminal_eq_postpayment_book
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The signed stopped right-payment correction in P3's exact canonical terminal notation. -/
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
        Real.exp (-(q * (S : ℝ))) * w (x + X.X S ω - rightLimit D S ω)
      else 0) ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
      else 0) := by
  have hc := avram_p3_c_bvchain_original_signed_horizon_cash_terminal_remainder
    X x C D hD w hjump ω S hS q hq
  have hterm :
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (x + X.X S ω - rightLimit D S ω)
      else 0) =
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (riskProcess X x D S ω - (rightLimit D S ω - D S ω))
      else 0) := by
    by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
    · simp only [if_pos hs]
      congr 1
      unfold riskProcess
      ring
    · simp only [if_neg hs]
  rw [hterm]
  exact hc
