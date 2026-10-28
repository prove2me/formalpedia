-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:52:30.138383+00:00
-- url     : https://prove2.me/submissions/d74a2360-4db4-4770-a3e7-2d63b650208c

import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_reward_eq_survival_integral
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_exp_survival_drift_integral
import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
  rw [bv_finite_activity_zero_reflected_reward_eq_survival_integral X hX q hq hBV hFinite]
  rw [bv_finite_activity_exp_survival_drift_integral X.drift q
    ((X.ν (Iio (0 : ℝ))).toReal) hq ENNReal.toReal_nonneg]
