-- Prove2me | solution 1 for Erdos287.triangle_additive_weight_harmonic_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:07:39.425724+00:00
-- url     : https://prove2.me/submissions/74b99caa-20a9-49e2-9367-b3e663ec6bd6

import Mathlib

open Finset

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The two additive parameters of a primitive triangle contribute only
one harmonic factor when weighted by the reciprocal square of their sum. -/
theorem solution (B : ℕ) :
    (∑ i ∈ Finset.range B, ∑ j ∈ Finset.range B, (1 : ℚ) / ((i : ℚ) + j + 2) ^ 2)
      ≤ ∑ i ∈ Finset.range B, (1 : ℚ) / ((i : ℚ) + 1) := by
  apply sum_le_sum
  intro i hi
  let a : ℚ := (i : ℚ) + 1
  have hshift (j : ℕ) : (i : ℚ) + j + 2 = a + j + 1 := by dsimp [a]; ring
  simp_rw [hshift]
  change (∑ j ∈ range B, (1 : ℚ) / (a + j + 1) ^ 2) ≤ 1 / a
  have hterm (j : ℕ) : (1 : ℚ) / (a + j + 1) ^ 2 ≤
      (1 : ℚ) / (a + j) - (1 : ℚ) / (a + j + 1) := by
    have ha : 0 < a + (j : ℚ) := by dsimp [a]; positivity
    have hb : 0 < a + (j : ℚ) + 1 := by linarith
    calc
      _ ≤ (1 : ℚ) / ((a + j) * (a + j + 1)) :=
        one_div_le_one_div_of_le (mul_pos ha hb) (by nlinarith)
      _ = _ := by
        field_simp [ha.ne', hb.ne']; ring
  have htel (N : ℕ) :
      (∑ j ∈ range N, ((1 : ℚ) / (a + j) - 1 / (a + j + 1))) =
        1 / a - 1 / (a + N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih, Nat.cast_succ]
      simp only [← add_assoc]
      ring
  calc
    _ ≤ ∑ j ∈ range B, ((1 : ℚ) / (a + j) - 1 / (a + j + 1)) :=
      sum_le_sum fun j _ => hterm j
    _ = 1 / a - 1 / (a + B) := htel B
    _ ≤ _ := sub_le_self _ (by dsimp [a]; positivity)

