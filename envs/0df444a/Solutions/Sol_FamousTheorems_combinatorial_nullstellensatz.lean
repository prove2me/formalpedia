-- Prove2me | solution 1 for FamousTheorems.combinatorial_nullstellensatz
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:29:34.417986+00:00
-- url     : https://prove2.me/submissions/97a97ac3-03ce-4313-99e4-77e66df87dd8

import Mathlib

theorem solution {R σ : Type*} [CommRing R] [IsDomain R] [Finite σ] (f : MvPolynomial σ R) (t : σ →₀ ℕ)
    (ht : MvPolynomial.coeff t f ≠ 0) (ht' : f.totalDegree = Finsupp.degree t) (S : σ → Finset R)
    (htS : ∀ i, t i < (S i).card) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ MvPolynomial.eval s f ≠ 0 :=
  MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero f t ht ht' S htS
