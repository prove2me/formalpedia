-- Prove2me | solution 1 for FamousTheorems.euler_four_square_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:28:06.822552+00:00
-- url     : https://prove2.me/submissions/d7d329a3-f0b0-46f3-956a-b7b047aaebef

import Mathlib

theorem solution {R : Type*} [CommRing R] (a b c d x y z w : R) :
    (a * x - b * y - c * z - d * w) ^ 2 + (a * y + b * x + c * w - d * z) ^ 2 +
        (a * z - b * w + c * x + d * y) ^ 2 + (a * w + b * z - c * y + d * x) ^ 2 =
      (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * (x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) :=
  euler_four_squares a b c d x y z w
