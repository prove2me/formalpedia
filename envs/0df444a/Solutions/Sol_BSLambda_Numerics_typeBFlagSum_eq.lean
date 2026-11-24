-- Prove2me | solution 1 for BSLambda.Numerics.typeBFlagSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:29:53.12084+00:00
-- url     : https://prove2.me/submissions/b63f4b96-ead5-4feb-8b32-6a165d480dbf

import Mathlib



theorem solution :
    Nat.choose 3502 3 + 2 * 3502 * Nat.choose 3501 2 + Nat.choose 3502 2 * 3500 =
      71519595000 := by
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
