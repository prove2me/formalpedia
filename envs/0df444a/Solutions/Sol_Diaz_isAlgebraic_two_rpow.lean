-- Prove2me | solution 1 for Diaz.isAlgebraic_two_rpow
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T08:24:15.09552+00:00
-- url     : https://prove2.me/submissions/a22a4651-f3f8-4819-b0fa-5f8cfac2493e

import Mathlib


section
open ComplexConjugate

theorem solution (q : ℚ) : IsAlgebraic ℚ ((2 : ℝ) ^ (q : ℝ)) := by
  refine ⟨Polynomial.X ^ q.den - Polynomial.C ((2 : ℚ) ^ q.num), ?_, ?_⟩
  · exact (Polynomial.monic_X_pow_sub_C _ q.den_nz).ne_zero
  · have hden : (q.den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hq : (q : ℝ) * (q.den : ℝ) = (q.num : ℝ) := by
      have h : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
        exact_mod_cast (Rat.num_div_den q).symm
      rw [h]; field_simp
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (q : ℝ)) q.den, ← Real.rpow_mul (by norm_num), hq,
      Real.rpow_intCast 2 q.num]
    push_cast
    norm_num
end
