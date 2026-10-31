-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_weighted_interval_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:50:28.625921+00:00
-- url     : https://prove2.me/submissions/15f17bbe-e760-40e8-b3ef-e4b7057598fb

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory intervalIntegral Set

/-- Exponential damping of a backward Taylor integral is bounded by
    damping evaluated at the translated positive state. -/
theorem solution
    (F : ℝ → ℝ) (x r θ : ℝ)
    (hr : 0 ≤ r) (hθ : 0 ≤ θ)
    (hI : IntervalIntegrable (fun s : ℝ => (r - s) * F (x - s)) volume 0 r)
    (hJ : IntervalIntegrable
      (fun s : ℝ => (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
      volume 0 r) :
    Real.exp (-θ * x) *
      |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)| ≤
      ∫ s in (0 : ℝ)..r,
        (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| := by
  have hconst : 0 ≤ Real.exp (-θ * x) := (Real.exp_pos _).le
  have hp : ∀ s ∈ Icc (0 : ℝ) r,
      Real.exp (-θ * x) * |(r - s) * F (x - s)| ≤
      (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| := by
    intro s hs
    have hsr : 0 ≤ r - s := sub_nonneg.mpr hs.2
    have hse : Real.exp (-θ * x) ≤ Real.exp (-θ * (x - s)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hθ hs.1])
    rw [abs_mul, abs_of_nonneg hsr]
    calc
      Real.exp (-θ * x) * ((r - s) * |F (x - s)|) =
          ((r - s) * |F (x - s)|) * Real.exp (-θ * x) := by ring
      _ ≤ ((r - s) * |F (x - s)|) * Real.exp (-θ * (x - s)) :=
        mul_le_mul_of_nonneg_left hse (mul_nonneg hsr (abs_nonneg _))
      _ = (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| := by ring
  calc
    Real.exp (-θ * x) *
      |∫ s in (0 : ℝ)..r, (r - s) * F (x - s)| ≤
        Real.exp (-θ * x) *
          (∫ s in (0 : ℝ)..r, |(r - s) * F (x - s)|) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.abs_integral_le_integral_abs hr) hconst
    _ = ∫ s in (0 : ℝ)..r,
        Real.exp (-θ * x) * |(r - s) * F (x - s)| := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ ∫ s in (0 : ℝ)..r,
      (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)| :=
      intervalIntegral.integral_mono_on hr (hI.abs.const_mul _)
        hJ hp
