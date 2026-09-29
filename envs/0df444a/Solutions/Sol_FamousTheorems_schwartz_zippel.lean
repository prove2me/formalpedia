-- Prove2me | solution 1 for FamousTheorems.schwartz_zippel
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:21:57.739234+00:00
-- url     : https://prove2.me/submissions/ff87e1fb-ae24-43bb-bb28-30cd8f15e55e

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R] {n : ℕ} {p : MvPolynomial (Fin n) R}
    (hp : p ≠ 0) (S : Fin n → Finset R) :
    (({x ∈ Fintype.piFinset fun i => S i | MvPolynomial.eval x p = 0}.card : NNRat) /
        ∏ i, ((S i).card : NNRat)) ≤
      p.support.sup fun s => ∑ i, ((s i : NNRat) / (S i).card) :=
  MvPolynomial.schwartz_zippel_sup_sum hp S
