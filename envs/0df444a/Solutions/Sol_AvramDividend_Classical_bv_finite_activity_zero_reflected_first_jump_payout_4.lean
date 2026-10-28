-- Prove2me | solution 4 for AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:20:18.564994+00:00
-- url     : https://prove2.me/submissions/400d5fb0-7881-463e-a83f-6eb44103d0aa

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_reward_eq_survival_integral
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_exp_survival_drift_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The stopped zero-barrier reward is the drift divided by the combined
discount and finite negative-jump intensity, using exact survival valuation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
  calc
    barrierSupValue X 0 q = ENNReal.ofReal
      (∫ t : ℝ in Ioi (0 : ℝ),
        X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
          ∂volume) :=
      bv_finite_activity_zero_reflected_reward_eq_survival_integral
        X hX q hq hBV hFinite
    _ = ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :=
      congrArg ENNReal.ofReal
        (bv_finite_activity_exp_survival_drift_integral
          X.drift q _ hq ENNReal.toReal_nonneg)
