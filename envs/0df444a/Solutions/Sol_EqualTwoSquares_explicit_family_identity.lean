-- Prove2me | solution 1 for EqualTwoSquares.explicit_family_identity
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:16.836308+00:00
-- url     : https://prove2.me/submissions/804147f3-be38-49ea-adfb-53daede8bc64

-- Public-mission submission for EqualTwoSquares.explicit_family_identity.

import Mathlib

theorem solution (n : ℤ) :
    (1 : ℤ)^2 + (n^2 - n + 1)^2 = (2 * n - 1)^2 + (n^2 - n - 1)^2 := by
  ring
