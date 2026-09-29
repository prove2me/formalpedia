-- Prove2me | solution 1 for FamousTheorems.mason_stothers
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:22:21.411426+00:00
-- url     : https://prove2.me/submissions/6e66cea3-3cfd-4bfd-b7a8-ff91daee7fd4

import Mathlib

theorem solution {k : Type*} [Field k] [DecidableEq k] {a b c : Polynomial k} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : c ≠ 0) (hab : IsCoprime a b) (hsum : a + b + c = 0) :
    (a.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree ∧
        b.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree ∧
        c.natDegree + 1 ≤ (UniqueFactorizationMonoid.radical (a * b * c)).natDegree) ∨
      (Polynomial.derivative a = 0 ∧ Polynomial.derivative b = 0 ∧ Polynomial.derivative c = 0) :=
  Polynomial.abc ha hb hc hab hsum
