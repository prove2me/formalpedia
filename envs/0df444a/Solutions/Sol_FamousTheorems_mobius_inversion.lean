-- Prove2me | solution 1 for FamousTheorems.mobius_inversion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:48.395808+00:00
-- url     : https://prove2.me/submissions/8dcbe797-0128-4662-8139-a3005d7ecabe

import Mathlib

theorem solution {R : Type*} [NonAssocRing R] {f g : ℕ → R} :
    (∀ n > 0, ∑ i ∈ n.divisors, f i = g n) ↔
      ∀ n > 0, ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : R) * g x.2 = f n :=
  ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
