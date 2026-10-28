-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_zero_reflected_first_jump_payout
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:54:39.810524+00:00
-- url     : https://prove2.me/submissions/5cdb2b66-1554-4626-9c4f-ee5ddb8a8145

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_reward_eq_survival_integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The first-jump survival-integral law reduces exactly to the stopped payout ratio. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    barrierSupValue X 0 q =
      ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
  let rate : ℝ := (X.ν (Iio (0 : ℝ))).toReal
  have hrate : 0 ≤ rate := ENNReal.toReal_nonneg
  have hqrate : 0 < q + rate := add_pos_of_pos_of_nonneg hq hrate
  have hIntegral :
      (∫ t : ℝ in Ioi (0 : ℝ),
        X.drift * Real.exp (-(q + rate) * t) ∂volume) =
        X.drift / (q + rate) := by
    rw [integral_const_mul, integral_exp_mul_Ioi
      (show -(q + rate) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ne_of_gt hqrate] <;> ring
  calc
    barrierSupValue X 0 q =
        ENNReal.ofReal
          (∫ t : ℝ in Ioi (0 : ℝ),
            X.drift * Real.exp (-(q + rate) * t) ∂volume) := by
          simpa only [rate] using
            bv_finite_activity_zero_reflected_reward_eq_survival_integral
              X hX q hq hBV hFinite
    _ = ENNReal.ofReal (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
      simpa only [rate] using congrArg ENNReal.ofReal hIntegral
