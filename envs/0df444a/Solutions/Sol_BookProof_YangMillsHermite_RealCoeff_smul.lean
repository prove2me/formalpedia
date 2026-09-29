-- Prove2me | solution 1 for BookProof.YangMillsHermite.RealCoeff.smul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:55:08.548437+00:00
-- url     : https://prove2.me/submissions/adefcd9c-53d6-4b9f-a513-a90fb647a72d

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false

theorem solution {d : ℕ} {t : ℝ} {p : MvPolynomial (Fin d) ℂ}
    (hp : MvPolynomial.map (starRingEnd ℂ) p = p) :
    MvPolynomial.map (starRingEnd ℂ) ((t : ℂ) • p) = (t : ℂ) • p := by
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Complex.conj_ofReal, hp]
#print axioms solution
