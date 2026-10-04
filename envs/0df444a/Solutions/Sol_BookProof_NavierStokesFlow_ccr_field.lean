-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ccr_field
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:15:01.495175+00:00
-- url     : https://prove2.me/submissions/9f7613eb-4b8e-4c31-b9b1-6bd73a07c00a

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic

-- Direct proof from the registered statement using Mathlib.
theorem solution {σ : Type*} [DecidableEq σ] (a b : σ) (p : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv a) (MvPolynomial.X b * p)
      - MvPolynomial.X b * (MvPolynomial.pderiv a) p = (if a = b then p else 0) := by
  by_cases h : a = b
  · subst b
    simp [MvPolynomial.pderiv_mul]
  · simp [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne (Ne.symm h), h]

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
