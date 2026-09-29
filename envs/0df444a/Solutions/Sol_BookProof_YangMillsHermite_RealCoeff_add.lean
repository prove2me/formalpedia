-- Prove2me | solution 1 for BookProof.YangMillsHermite.RealCoeff.add
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:06.671295+00:00
-- url     : https://prove2.me/submissions/5b6a10d8-75e4-475d-ba59-18c7676d963f

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

theorem solution {d : ℕ} {p q : MvPolynomial (Fin d) ℂ}
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p)
    (hq : MvPolynomial.map (starRingEnd ℂ) q = q) :
    MvPolynomial.map (starRingEnd ℂ) (p + q) = p + q := by
  rw [map_add, hp, hq]
#print axioms solution
