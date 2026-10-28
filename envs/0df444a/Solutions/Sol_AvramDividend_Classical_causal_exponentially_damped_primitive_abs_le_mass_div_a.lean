-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponentially_damped_primitive_abs_le_mass_div_a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:30:08.528921+00:00
-- url     : https://prove2.me/submissions/bf037577-8e45-4d8b-afd1-acef3b56c839

import Mathlib

open MeasureTheory Set
theorem solution
    (P F : ℝ → ℝ) (a w x M : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x)
    (hPint : IntervalIntegrable
      (fun s : ℝ => Real.exp (-w * (x - s)) * P s) volume 0 x)
    (hFint : IntervalIntegrable F volume 0 x)
    (hdom : ∀ s ∈ Ioo (0 : ℝ) x, |P s| ≤ F s)
    (hMass : ∫ s in (0 : ℝ)..x, F s ≤ M) :
    |(∫ s in (0 : ℝ)..x, Real.exp (-w * (x - s)) * P s) / a| ≤ M / a := by
  rw [abs_div, abs_of_pos ha]
  refine div_le_div_of_nonneg_right ?_ ha.le
  refine le_trans (intervalIntegral.abs_integral_le_integral_abs hx.le) (le_trans ?_ hMass)
  refine intervalIntegral.integral_mono_on_of_le_Ioo hx.le hPint.abs hFint fun s hs => ?_
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-w * (x - s)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [hs.2])
  calc Real.exp (-w * (x - s)) * |P s| ≤ 1 * |P s| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |P s| := one_mul _
    _ ≤ F s := hdom s hs
