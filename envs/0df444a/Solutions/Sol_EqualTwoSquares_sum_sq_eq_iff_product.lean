-- Prove2me | solution 1 for EqualTwoSquares.sum_sq_eq_iff_product
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:25.352061+00:00
-- url     : https://prove2.me/submissions/5119315e-6eb9-4313-adf2-3c1fa2e42506

-- Public-mission submission for EqualTwoSquares.sum_sq_eq_iff_product.

import Mathlib

theorem solution (a b c d : ℤ) :
    a^2 + b^2 = c^2 + d^2 ↔ (a + c) * (a - c) = (d + b) * (d - b) := by
  constructor
  · intro h
    nlinarith [show (a + c) * (a - c) = a^2 - c^2 by ring,
      show (d + b) * (d - b) = d^2 - b^2 by ring]
  · intro h
    nlinarith [show (a + c) * (a - c) = a^2 - c^2 by ring,
      show (d + b) * (d - b) = d^2 - b^2 by ring]
