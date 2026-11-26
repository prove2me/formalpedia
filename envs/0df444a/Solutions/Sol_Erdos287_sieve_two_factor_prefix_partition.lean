-- Prove2me | solution 1 for Erdos287.sieve_two_factor_prefix_partition
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:47:35.542107+00:00
-- url     : https://prove2.me/submissions/a8cf1043-cf47-4755-9953-c329f105962f

import Mathlib

set_option autoImplicit false

/-- The logarithms of the prime factors in a linear sieve support can be
partitioned between two prescribed logarithmic size bounds. -/
theorem solution (xs : List ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hprefix : ∀ (l : List ℝ) (x : ℝ) (r : List ℝ), xs = l ++ x :: r →
      l.sum + x + x ≤ a + b) :
    ∃ left right : List ℝ, xs.Perm (left ++ right) ∧
      left.sum ≤ a ∧ right.sum ≤ b := by
  induction xs generalizing a b with
  | nil =>
    exact ⟨[], [], List.Perm.nil, ha, hb⟩
  | cons x xs ih =>
    have hhead : x + x ≤ a + b := by
      simpa using hprefix [] x xs rfl
    have htail (l : List ℝ) (y : ℝ) (r : List ℝ) (hl : xs = l ++ y :: r) :
        x + l.sum + y + y ≤ a + b := by
      exact hprefix (x :: l) y r (congrArg (List.cons x) hl)
    by_cases hxa : x ≤ a
    · obtain ⟨left, right, hp, hl, hr⟩ :=
        ih (a - x) b (sub_nonneg.mpr hxa) hb (by
          intro l y r hl
          linarith [htail l y r hl])
      refine ⟨x :: left, right, List.Perm.cons x hp, ?_, hr⟩
      simp only [List.sum_cons]
      linarith
    · have hxb : x ≤ b := by linarith
      obtain ⟨left, right, hp, hl, hr⟩ :=
        ih a (b - x) ha (sub_nonneg.mpr hxb) (by
          intro l y r hl
          linarith [htail l y r hl])
      refine ⟨left, x :: right, (List.Perm.cons x hp).trans List.perm_middle.symm, hl, ?_⟩
      simp only [List.sum_cons]
      linarith

