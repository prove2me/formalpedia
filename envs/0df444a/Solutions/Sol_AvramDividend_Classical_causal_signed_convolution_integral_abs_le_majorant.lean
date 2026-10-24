-- Prove2me | solution 1 for AvramDividend.Classical.causal_signed_convolution_integral_abs_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:08:55.857593+00:00
-- url     : https://prove2.me/submissions/b165c9cd-84ca-41ae-9325-c4b7c5768ce1

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Causal integral domination transfers the absolute signed convolution to a positive envelope. -/
theorem solution
    (k κ f F : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hint : IntervalIntegrable (fun s : ℝ => k (x - s) * f s) volume 0 x)
    (hmajor : IntervalIntegrable (fun s : ℝ => κ (x - s) * F s) volume 0 x)
    (hk : ∀ s ∈ Ioo (0 : ℝ) x, |k (x - s)| ≤ κ (x - s))
    (hf : ∀ s ∈ Ioo (0 : ℝ) x, |f s| ≤ F s)
    (hκ : ∀ s ∈ Ioo (0 : ℝ) x, 0 ≤ κ (x - s)) :
    |∫ s in (0 : ℝ)..x, k (x - s) * f s| ≤
      ∫ s in (0 : ℝ)..x, κ (x - s) * F s := by
  have hpoint : ∀ s ∈ Ioo (0 : ℝ) x,
      |k (x - s) * f s| ≤ κ (x - s) * F s := by
    intro s hs
    calc
      |k (x - s) * f s|
          = |k (x - s)| * |f s| := abs_mul _ _
      _ ≤ κ (x - s) * |f s| :=
          mul_le_mul_of_nonneg_right (hk s hs) (abs_nonneg _)
      _ ≤ κ (x - s) * F s :=
          mul_le_mul_of_nonneg_left (hf s hs) (hκ s hs)
  calc
    |∫ s in (0 : ℝ)..x, k (x - s) * f s|
        ≤ ∫ s in (0 : ℝ)..x, |k (x - s) * f s| :=
          intervalIntegral.abs_integral_le_integral_abs hx.le
    _ ≤ ∫ s in (0 : ℝ)..x, κ (x - s) * F s :=
          intervalIntegral.integral_mono_on_of_le_Ioo
            hx.le hint.abs hmajor hpoint
