-- Prove2me | solution 1 for BirkhoffGlobalSection.outer_inverse_distance_potential_min
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T23:27:58.631617+00:00
-- url     : https://prove2.me/submissions/9294ae91-34dd-4aa8-8bb4-d37d9c6f34a5

import Mathlib
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

theorem solution (a A B u v : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : 0 < u) (hv : 0 < v)
    (hbal : u + a = A / u ^ 2 + B / (1 + u) ^ 2) :
    (u + a) ^ 2 / 2 + A / u + B / (1 + u) ≤
      (v + a) ^ 2 / 2 + A / v + B / (1 + v) := by
  have hq : (u + a) ^ 2 / 2 + (u + a) * (v - u) ≤
      (v + a) ^ 2 / 2 := by nlinarith [sq_nonneg (v - u)]
  have hrec₁ : A / u - A / u ^ 2 * (v - u) ≤ A / v := by
    have heq : A / v - A / u + A / u ^ 2 * (v - u) =
        A * (v - u) ^ 2 / (u ^ 2 * v) := by
      have hune : u ≠ 0 := ne_of_gt hu
      have hvne : v ≠ 0 := ne_of_gt hv
      field_simp <;> ring
    have hge : 0 ≤ A * (v - u) ^ 2 / (u ^ 2 * v) :=
      div_nonneg (mul_nonneg hA (sq_nonneg _))
        (le_of_lt (mul_pos (sq_pos_of_pos hu) hv))
    linarith
  have hrec₂ : B / (1 + u) - B / (1 + u) ^ 2 * (v - u) ≤
      B / (1 + v) := by
    have hpu : 0 < 1 + u := by linarith
    have hpv : 0 < 1 + v := by linarith
    have heq : B / (1 + v) - B / (1 + u) + B / (1 + u) ^ 2 * (v - u) =
        B * (v - u) ^ 2 / ((1 + u) ^ 2 * (1 + v)) := by
      have hune : 1 + u ≠ 0 := ne_of_gt hpu
      have hvne : 1 + v ≠ 0 := ne_of_gt hpv
      field_simp <;> ring
    have hge : 0 ≤ B * (v - u) ^ 2 / ((1 + u) ^ 2 * (1 + v)) :=
      div_nonneg (mul_nonneg hB (sq_nonneg _))
        (le_of_lt (mul_pos (sq_pos_of_pos hpu) hpv))
    linarith
  have heq := congrArg (fun z : ℝ => z * (v - u)) hbal
  linarith
