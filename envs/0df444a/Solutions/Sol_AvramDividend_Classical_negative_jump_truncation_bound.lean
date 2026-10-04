-- Prove2me | solution 1 for AvramDividend.Classical.negative_jump_truncation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:07:58.843359+00:00
-- url     : https://prove2.me/submissions/509ea3c0-8dc1-48b3-a827-3c6025f369dc

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (y : ℝ) :
    min ((Real.toNNReal (-y) : ℝ)) 1 ≤
      (Ioo (-1 : ℝ) 0).indicator (fun x : ℝ => |x|) y +
        min 1 (y ^ 2) := by
  rw [Real.coe_toNNReal']
  have hind : 0 ≤ (Ioo (-1 : ℝ) 0).indicator (fun x : ℝ => |x|) y :=
    Set.indicator_nonneg (fun x _ => abs_nonneg x) y
  rcases le_or_gt 0 y with h0 | h0
  · have : max (-y) 0 = 0 := max_eq_right (by linarith)
    rw [this]
    have h1 : (0:ℝ) ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg y)
    calc min (0:ℝ) 1 ≤ 0 := min_le_left _ _
      _ ≤ _ := by linarith
  · rcases le_or_gt y (-1) with h1 | h1
    · have hy2 : 1 ≤ y ^ 2 := by nlinarith
      rw [min_eq_left hy2]
      calc min (max (-y) 0) 1 ≤ 1 := min_le_right _ _
        _ ≤ _ := by linarith
    · have hmem : y ∈ Ioo (-1 : ℝ) 0 := ⟨h1, h0⟩
      rw [Set.indicator_of_mem hmem, abs_of_neg h0, max_eq_left (by linarith)]
      have h2 : (0:ℝ) ≤ min 1 (y ^ 2) := le_min zero_le_one (sq_nonneg y)
      calc min (-y) 1 ≤ -y := min_le_left _ _
        _ ≤ _ := by linarith
