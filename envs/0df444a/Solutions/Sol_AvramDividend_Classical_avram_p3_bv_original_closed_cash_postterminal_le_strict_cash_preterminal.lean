-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_closed_cash_postterminal_le_strict_cash_preterminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:51:31.595482+00:00
-- url     : https://prove2.me/submissions/b844624d-b14f-4126-ac15-96397e1e3341

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/- The active closed-horizon right payment is paid out of the prepayment
terminal value, including the survival/ruin boundary distinction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (S : ℝ≥0) (hS : 0 < S)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ ω : Ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) *
          w (x + X.X S ω - rightLimit D S ω)
       else 0) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω)
       else 0) := by
  intro ω
  rw [avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
    X x C D hD ω q hq S]
  have hS0 : S ≠ 0 := ne_of_gt hS
  by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hslope :=
      avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
        X x D w q hjump ω S (Or.inr hs)
    simp only [hs, if_true, hS0, false_or]
    linarith
  · simp [hs, hS0]
