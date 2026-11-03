-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:52:59.188625+00:00
-- url     : https://prove2.me/submissions/e5d70ad0-fda8-4f33-a01f-28adf4b2659d

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

/-- Quantitative real-valued lower bound on a common original zero-cap
BV dividend allowance: the exact positive reflected payout is necessary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W := by
  have hDen : 0 < q + (X.ν (Iio (0 : ℝ))).toReal := by
    have hm : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal := ENNReal.toReal_nonneg
    linarith
  have hRatio : 0 <
      X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    div_pos (bv_standing_drift_pos X hX hBV).1 hDen
  have hBound :=
    avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
      X hX hBV hFinite q hq W hUniform
  by_contra hNo
  have hLt : W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) :=
    lt_of_not_ge hNo
  have hStrict :
      ENNReal.ofReal W <
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :=
    (ENNReal.ofReal_lt_ofReal_iff hRatio).mpr hLt
  exact (not_lt_of_ge hBound) hStrict
