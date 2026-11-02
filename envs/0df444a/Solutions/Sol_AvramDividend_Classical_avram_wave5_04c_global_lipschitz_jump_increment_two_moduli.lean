-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:07:13.194536+00:00
-- url     : https://prove2.me/submissions/78851357-5f33-4cdd-b4e9-98aeb33b157c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false

theorem solution (w : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x z y : ℝ) :
    |(w (z + y) - w z) - (w (x + y) - w x)|
      ≤ 2 * L * min |z - x| |y| := by
  have hx :
      |(w (z + y) - w z) - (w (x + y) - w x)|
        ≤ 2 * L * |z - x| := by
    calc
      _ = |(w (z + y) - w (x + y)) + (w x - w z)| := by congr 1 <;> ring
      _ ≤ |w (z + y) - w (x + y)| + |w x - w z| := abs_add_le _ _
      _ ≤ L * |(z + y) - (x + y)| + L * |x - z| :=
        add_le_add (hLip (z + y) (x + y)) (hLip x z)
      _ = 2 * L * |z - x| := by
        rw [show (z + y) - (x + y) = z - x by ring, abs_sub_comm x z]
        ring
  have hy :
      |(w (z + y) - w z) - (w (x + y) - w x)|
        ≤ 2 * L * |y| := by
    calc
      _ ≤ |(w (z + y) - w z) - 0| + |0 - (w (x + y) - w x)| :=
        abs_sub_le _ _ _
      _ = |w (z + y) - w z| + |w (x + y) - w x| := by
        simp only [sub_zero, zero_sub, abs_neg]
      _ ≤ L * |(z + y) - z| + L * |(x + y) - x| :=
        add_le_add (hLip (z + y) z) (hLip (x + y) x)
      _ = 2 * L * |y| := by
        rw [show (z + y) - z = y by ring,
          show (x + y) - x = y by ring]
        ring
  rcases le_total |z - x| |y| with h | h
  · rw [min_eq_left h]
    exact hx
  · rw [min_eq_right h]
    exact hy
