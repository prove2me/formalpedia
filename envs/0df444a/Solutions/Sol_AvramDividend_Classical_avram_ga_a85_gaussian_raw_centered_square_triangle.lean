-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a85_gaussian_raw_centered_square_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:06:21.038231+00:00
-- url     : https://prove2.me/submissions/f8118281-3186-440b-b108-f87813add872

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The original physical source raw-centred square difference has a direct scalar triangle bound. -/
theorem solution (z d : ℝ) :
    |(z + d)^2 - z^2| ≤ 2 * |d| * |z| + d^2 := by
  have hEq : (z + d)^2 - z^2 = 2 * d * z + d^2 := by ring
  rw [hEq]
  calc
    |2 * d * z + d^2| ≤ |2 * d * z| + |d^2| := abs_add_le _ _
    _ = 2 * |d| * |z| + d^2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      rw [abs_pow, sq_abs] <;> ring
