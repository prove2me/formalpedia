-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_weighted_integral_moment_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:44:40.300717+00:00
-- url     : https://prove2.me/submissions/76684eb1-2568-4980-aeba-e9b6d1ffbf0a

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (k : ℕ)
    (hzero : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ)
    (hk : IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ) :
    (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
      (Real.exp (θ * y) - 1) ^ 4 ∂μ) ≤
    (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂μ) := by
  apply integral_mono_ae hk hzero
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hnonpos : θ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
  have hExp : Real.exp (θ * y) ≤ 1 :=
    (Real.exp_le_one_iff).2 hnonpos
  have hPower : (Real.exp (θ * y)) ^ k ≤ 1 := by
    exact pow_le_one₀ (le_of_lt (Real.exp_pos _)) hExp
  have hWeight : 0 ≤ (Real.exp (θ * y) - 1) ^ 4 := by positivity
  calc
    (Real.exp (θ * y)) ^ k * (Real.exp (θ * y) - 1) ^ 4 ≤
        1 * (Real.exp (θ * y) - 1) ^ 4 :=
      mul_le_mul_of_nonneg_right hPower hWeight
    _ = (Real.exp (θ * y) - 1) ^ 4 := one_mul _
