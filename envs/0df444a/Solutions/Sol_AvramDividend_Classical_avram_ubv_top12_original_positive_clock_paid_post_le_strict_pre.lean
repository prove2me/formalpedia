-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_positive_clock_paid_post_le_strict_pre
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T21:48:03.634849+00:00
-- url     : https://prove2.me/submissions/27ff66c4-c4b3-49d3-9b67-b8edd0097cab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Original positive-clock endpoint comparison used in the strict Gaussian budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (S : ℝ≥0) (hSpos : 0 < S) :
    Real.exp (-(q * (S : ℝ))) *
      w (if (S : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X S ω - rightLimit D S ω
      else riskProcess X x D S ω) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal ≤
    Real.exp (-(q * (S : ℝ))) * w (riskProcess X x D S ω) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (S : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal := by
  have hcash := avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
    X x C D hD ω q hq S
  rw [hcash]
  by_cases hs : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hactive : S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω := Or.inr hs
    have hj := hjump ω S hactive
    have hpost : riskProcess X x D S ω -
        (rightLimit D S ω - D S ω) =
        x + X.X S ω - rightLimit D S ω := by
      change (x + X.X S ω - D S ω) -
        (rightLimit D S ω - D S ω) = _
      ring
    rw [hpost] at hj
    simp only [if_pos hs, if_pos hactive]
    have he : 0 ≤ Real.exp (-(q * (S : ℝ))) :=
      (Real.exp_pos (-(q * (S : ℝ)))).le
    have hejump := mul_le_mul_of_nonneg_left hj he
    linarith
  · have hinactive : ¬ (S = 0 ∨ (S : ℝ≥0∞) < ruinTime X x D ω) := by
      exact not_or_intro (ne_of_gt hSpos) hs
    simp only [if_neg hs, if_neg hinactive, add_zero]
    exact le_rfl
