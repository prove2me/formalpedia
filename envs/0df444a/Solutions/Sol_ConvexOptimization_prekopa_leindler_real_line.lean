-- Prove2me | solution 1 for ConvexOptimization.prekopa_leindler_real_line
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T04:50:30.522195+00:00
-- url     : https://prove2.me/submissions/dc62ef3a-57f0-45cb-984c-6f9c672f09d3

import Mathlib
import Theorems.Thm_ConvexOptimization_leindler_supremal_integral_real_line

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution
    (l : ℝ) (hl0 : 0 < l) (hl1 : l < 1)
    (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hple : ∀ x y : ℝ,
      f x ^ (1 - l) * g y ^ l ≤ h ((1 - l) • x + l • y)) :
    (∫⁻ x, f x) ^ (1 - l) * (∫⁻ x, g x) ^ l ≤ ∫⁻ x, h x := by
  refine (ConvexOptimization.leindler_supremal_integral_real_line
    l hl0 hl1 f g hf hg).trans ?_
  apply lintegral_mono
  intro z
  apply sSup_le
  intro q hq
  rcases hq with ⟨x, y, hxy, rfl⟩
  rw [← hxy]
  exact hple x y
