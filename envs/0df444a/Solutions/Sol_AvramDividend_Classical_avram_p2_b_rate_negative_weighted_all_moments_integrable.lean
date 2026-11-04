-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_weighted_all_moments_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:44:48.639191+00:00
-- url     : https://prove2.me/submissions/17d21655-42a5-4d2b-b90e-108c4f648919

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
      (fun y : ℝ => (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ) :
    IntegrableOn
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) μ := by
  have hmeas : AEStronglyMeasurable
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4) (μ.restrict (Iio (0 : ℝ))) :=
    (by fun_prop : Measurable
      (fun y : ℝ => (Real.exp (θ * y)) ^ k *
        (Real.exp (θ * y) - 1) ^ 4)).aestronglyMeasurable
  refine hzero.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hnonpos : θ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy)
  have hExp : Real.exp (θ * y) ≤ 1 :=
    (Real.exp_le_one_iff).2 hnonpos
  have hPower : (Real.exp (θ * y)) ^ k ≤ 1 :=
    pow_le_one₀ (le_of_lt (Real.exp_pos _)) hExp
  have hWeight : 0 ≤ (Real.exp (θ * y) - 1) ^ 4 := by positivity
  have hWeighted : 0 ≤ (Real.exp (θ * y)) ^ k *
      (Real.exp (θ * y) - 1) ^ 4 := by positivity
  have hBound :
      (Real.exp (θ * y)) ^ k * (Real.exp (θ * y) - 1) ^ 4 ≤
        (Real.exp (θ * y) - 1) ^ 4 := by
    calc
      _ ≤ 1 * (Real.exp (θ * y) - 1) ^ 4 :=
        mul_le_mul_of_nonneg_right hPower hWeight
      _ = _ := one_mul _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hWeighted,
    abs_of_nonneg hWeight] using hBound
