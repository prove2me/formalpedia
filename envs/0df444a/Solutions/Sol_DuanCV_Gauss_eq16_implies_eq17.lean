-- Prove2me | solution 1 for DuanCV.Gauss.eq16_implies_eq17
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:45:20.814793+00:00
-- url     : https://prove2.me/submissions/6c2cc4fb-56c5-48c9-bce2-69a60dac8a4a

import Mathlib

theorem solution (n1 n2 m1 m2 c1 c2 a0 : ℝ) (ha0 : 0 < a0)
    (h1 : a0 ^ 4 * (n1 - 1) = m1 - 1) (h2 : a0 ^ 4 * (n2 - 1) = m2 - 1)
    (h11b : |c1| - |c2| =
      Real.sqrt ((n1 - 1) * (m1 - 1)) - Real.sqrt ((n2 - 1) * (m2 - 1)))
    (h16 : a0 ^ 2 + 1 / a0 ^ 2 ≤
      a0 ^ 2 * ((n1 + n2) / 2) + (m1 + m2) / (2 * a0 ^ 2) - |c1| - |c2|) :
    |c1| ≤ Real.sqrt ((n1 - 1) * (m1 - 1)) ∧ |c2| ≤ Real.sqrt ((n2 - 1) * (m2 - 1)) := by
  have hs : ∀ n m : ℝ, a0 ^ 4 * (n - 1) = m - 1 →
      Real.sqrt ((n - 1) * (m - 1)) = a0 ^ 2 * |n - 1| := by
    intro n m h
    rw [← h, show (n - 1) * (a0 ^ 4 * (n - 1)) = (a0 ^ 2 * |n - 1|) ^ 2 by
      rw [mul_pow, sq_abs]; ring]
    exact Real.sqrt_sq (by positivity)
  rw [hs n1 m1 h1, hs n2 m2 h2] at h11b ⊢
  have hm1 : m1 = a0 ^ 4 * (n1 - 1) + 1 := by linarith
  have hm2 : m2 = a0 ^ 4 * (n2 - 1) + 1 := by linarith
  have ha2 : 0 < a0 ^ 2 := by positivity
  have hfrac : (m1 + m2) / (2 * a0 ^ 2) = a0 ^ 2 * ((n1 - 1) + (n2 - 1)) / 2 + 1 / a0 ^ 2 := by
    rw [hm1, hm2]; field_simp; ring
  rw [hfrac] at h16
  have hsum : |c1| + |c2| ≤ a0 ^ 2 * ((n1 - 1) + (n2 - 1)) := by nlinarith
  have e1 : a0 ^ 2 * (n1 - 1) ≤ a0 ^ 2 * |n1 - 1| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) ha2.le
  have e2 : a0 ^ 2 * (n2 - 1) ≤ a0 ^ 2 * |n2 - 1| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) ha2.le
  constructor <;> nlinarith
