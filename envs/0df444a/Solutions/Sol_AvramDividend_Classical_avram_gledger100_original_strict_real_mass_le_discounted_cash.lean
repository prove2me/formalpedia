-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger100_original_strict_real_mass_le_discounted_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:48:40.243884+00:00
-- url     : https://prove2.me/submissions/4d2f4c49-340a-4359-9b0f-1a483a96d800

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger96_measurable_stopped_cash_discount_lower_mass
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive finite cash converts the ENNReal discount lower bound into real mass domination. -/
theorem solution
    (μ : Measure ℝ) (σ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) (b : ℝ≥0)
    (hsub : Ioo (0 : ℝ) (b : ℝ) ⊆ paymentTimes σ ∩ Iio (b : ℝ))
    (hfinite : (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) < ⊤) :
    (μ (Ioo (0 : ℝ) (b : ℝ))).toReal ≤
      Real.exp (q * (b : ℝ)) *
        (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by
  let S : Set ℝ := Ioo 0 (b : ℝ)
  have hLower : ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) * μ S ≤
      ∫⁻ t in S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ :=
    avram_gledger96_measurable_stopped_cash_discount_lower_mass
      q hq μ S measurableSet_Ioo (b : ℝ) (by intro t ht; exact le_of_lt ht.2)
  have hCash : (∫⁻ t in S,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) :=
    lintegral_mono_set hsub
  have hBound := hLower.trans hCash
  have hReal := ENNReal.toReal_mono (ne_of_lt hfinite) hBound
  rw [ENNReal.toReal_ofReal_mul _ _ (le_of_lt (Real.exp_pos _))] at hReal
  have hReal' : (μ S).toReal * Real.exp (-(q * (b : ℝ))) ≤
      (∫⁻ t in paymentTimes σ ∩ Iio (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by
    simpa only [mul_comm] using hReal
  have hDiv := (le_div_iff₀ (Real.exp_pos (-(q * (b : ℝ))))).2 hReal'
  simpa only [S, div_eq_mul_inv, Real.exp_neg, inv_inv, mul_comm] using hDiv
