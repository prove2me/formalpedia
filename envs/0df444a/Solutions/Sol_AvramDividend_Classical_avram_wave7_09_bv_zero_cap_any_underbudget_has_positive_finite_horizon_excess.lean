-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:53:06.709389+00:00
-- url     : https://prove2.me/submissions/bf6a15d2-bb35-46b5-96a4-5de31f2f417e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every allowance strictly below the exact reflected original BV value
is violated at an actual finite horizon, not merely at an infinite limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUnder : W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :
    ∃ n : ℕ, ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  have hDen : 0 < q + (X.ν (Iio (0 : ℝ))).toReal := by
    have hm : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal := ENNReal.toReal_nonneg
    linarith
  have hRatio : 0 <
      X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    div_pos (bv_standing_drift_pos X hX hBV).1 hDen
  by_contra hNo
  have hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W := by
    intro n
    by_contra hNotLe
    have hEx : ENNReal.ofReal W <
        (∫⁻ ω, ∫⁻ t in
          paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) :=
      lt_of_not_ge hNotLe
    exact hNo ⟨n, hEx⟩
  have hBound :=
    avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
      X hX hBV hFinite q hq W hUniform
  have hStrict :
      ENNReal.ofReal W <
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :=
    (ENNReal.ofReal_lt_ofReal_iff hRatio).mpr hUnder
  exact (not_lt_of_ge hBound) hStrict
