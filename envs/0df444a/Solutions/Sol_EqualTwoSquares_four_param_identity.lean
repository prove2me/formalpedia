-- Prove2me | solution 1 for EqualTwoSquares.four_param_identity
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:15.400643+00:00
-- url     : https://prove2.me/submissions/30d9df8a-b744-468e-83a1-b1773ab49a99

-- Public-mission submission for EqualTwoSquares.four_param_identity.

import Mathlib

theorem solution (p q r s : ℤ) :
    (p * r + q * s)^2 + (p * s - q * r)^2 =
      (p * r - q * s)^2 + (p * s + q * r)^2 := by
  ring
