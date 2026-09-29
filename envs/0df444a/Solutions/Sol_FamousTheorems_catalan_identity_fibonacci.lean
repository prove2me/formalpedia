-- Prove2me | solution 1 for FamousTheorems.catalan_identity_fibonacci
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:21:07.791496+00:00
-- url     : https://prove2.me/submissions/c5e458b2-5876-4b08-bc57-cea439f275b2

import Mathlib

theorem solution (x a : ℤ) : Int.fib (x + a) ^ 2 - Int.fib x * Int.fib (x + 2 * a) = (-1) ^ x.natAbs * Int.fib a ^ 2 :=
  Int.fib_add_sq_sub_fib_mul_fib_add_two_mul x a
