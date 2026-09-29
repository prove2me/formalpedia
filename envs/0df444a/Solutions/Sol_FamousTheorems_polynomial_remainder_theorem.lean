-- Prove2me | solution 1 for FamousTheorems.polynomial_remainder_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T21:45:00.338886+00:00
-- url     : https://prove2.me/submissions/448c9b40-527c-42b9-b247-5d4e1f6e51d9

import Mathlib

theorem solution {R : Type*} [CommRing R] (p : Polynomial R) (a : R) :
    p.modByMonic (Polynomial.X - Polynomial.C a) = Polynomial.C (p.eval a) := by
  exact Polynomial.modByMonic_X_sub_C_eq_C_eval p a
