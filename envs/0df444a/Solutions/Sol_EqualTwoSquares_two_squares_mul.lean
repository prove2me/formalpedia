-- Prove2me | solution 1 for EqualTwoSquares.two_squares_mul
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-26T12:01:14.061012+00:00
-- url     : https://prove2.me/submissions/d94543e8-e4c4-46ed-a621-665b45e06900

-- Public-mission submission for EqualTwoSquares.two_squares_mul.
-- Verified locally: see missions/two-squares/platform/statements/ and the combined
-- compile of every solution in missions/two-squares/platform/solutions/check_all.py.

import Mathlib

theorem solution {R : Type*} [CommRing R] (p q r s : R) :
    (p^2 + q^2) * (r^2 + s^2) = (p * r + q * s)^2 + (p * s - q * r)^2 ∧
      (p^2 + q^2) * (r^2 + s^2) = (p * r - q * s)^2 + (p * s + q * r)^2 := by
  constructor <;> ring
