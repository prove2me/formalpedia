-- Prove2me | solution 1 for EqualTwoSquares.family_scaling_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:23.920581+00:00
-- url     : https://prove2.me/submissions/d6a375bf-956e-44a8-9269-62294527ddad

-- Public-mission submission for EqualTwoSquares.family_scaling_trivial.

import Mathlib

theorem solution {m n k : ℤ}
    (h : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      k • ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1)) :
    n = m := by
  have hk : k = 1 := by
    have hcoord := congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.1) h
    simpa using hcoord.symm
  have hunit : ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1) =
      ((1 : ℤ), m^2 - m + 1, 2 * m - 1, m^2 - m - 1) := by
    rw [hk] at h
    simpa using h
  have hlin : 2 * n - 1 = 2 * m - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) hunit
  omega
