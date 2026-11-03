-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_iff_positive_horizon_cash_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:28:50.999026+00:00
-- url     : https://prove2.me/submissions/0ea24b0f-2c64-4f3c-9236-e06c0d559162

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original finite-activity BV zero-cap classification: a
subthreshold allowance is equivalent to strict overpayment at some
genuinely positive finite horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ↔
    ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  constructor
  · intro hUnder
    exact
      avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
        X hX hBV hFinite q hq W hUnder
  · rintro ⟨n, hnpos, hExcess⟩
    by_contra hNot
    have hThreshold :
        X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W :=
      le_of_not_gt hNot
    have hUniform :=
      (avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
        X hX hBV hFinite q hq W).mpr hThreshold
    exact (not_le_of_gt hExcess) (hUniform n)
