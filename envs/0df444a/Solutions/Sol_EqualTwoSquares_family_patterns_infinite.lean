-- Prove2me | solution 1 for EqualTwoSquares.family_patterns_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:22.566282+00:00
-- url     : https://prove2.me/submissions/d15ca80e-f645-467e-a2f3-d812bc02d408

-- Public-mission submission for EqualTwoSquares.family_patterns_infinite.

import Mathlib

theorem solution :
    (Set.range (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1))).Infinite := by
  apply Set.infinite_range_of_injective
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega
