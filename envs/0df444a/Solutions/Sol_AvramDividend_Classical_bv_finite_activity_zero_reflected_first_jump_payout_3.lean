-- Prove2me | solution 3 for AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:42:22.09873+00:00
-- url     : https://prove2.me/submissions/f8653205-7bb5-41f9-9a6e-a77c76bfc41e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_reward_eq_survival_integral
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_exp_survival_drift_integral
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
  have hrate : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal :=
    ENNReal.toReal_nonneg
  calc
    barrierSupValue X 0 q = ENNReal.ofReal
        (∫ t : ℝ in Ioi (0 : ℝ),
          X.drift * Real.exp (-(q + (X.ν (Iio (0 : ℝ))).toReal) * t)
            ∂volume) :=
      bv_finite_activity_zero_reflected_reward_eq_survival_integral
        X hX q hq hBV hFinite
    _ = ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
      rw [bv_finite_activity_exp_survival_drift_integral
        X.drift q (X.ν (Iio (0 : ℝ))).toReal hq hrate]
