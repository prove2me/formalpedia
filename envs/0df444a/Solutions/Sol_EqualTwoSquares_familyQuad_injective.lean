-- Prove2me | solution 1 for EqualTwoSquares.familyQuad_injective
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:21.214454+00:00
-- url     : https://prove2.me/submissions/dc755400-499f-4c5a-bd34-5b16e9c5e505

-- Public-mission submission for EqualTwoSquares.familyQuad_injective.

import Mathlib

theorem solution :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by
  intro m n h
  have hlin : 2 * m - 1 = 2 * n - 1 := by
    simpa using congrArg (fun t : ℤ × ℤ × ℤ × ℤ => t.2.2.1) h
  omega
