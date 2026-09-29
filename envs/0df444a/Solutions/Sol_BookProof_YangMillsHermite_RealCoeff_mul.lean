-- Prove2me | solution 1 for BookProof.YangMillsHermite.RealCoeff.mul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:07.685181+00:00
-- url     : https://prove2.me/submissions/5ebe8876-4861-4a00-926f-0d5b9c7b93c2

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

theorem solution {d : ℕ} {p q : MvPolynomial (Fin d) ℂ}
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p)
    (hq : MvPolynomial.map (starRingEnd ℂ) q = q) :
    MvPolynomial.map (starRingEnd ℂ) (p * q) = p * q := by
  rw [map_mul, hp, hq]
#print axioms solution
