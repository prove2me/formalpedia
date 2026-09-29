-- Prove2me | solution 1 for FamousTheorems.fermat_last_theorem_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:37.427513+00:00
-- url     : https://prove2.me/submissions/04c372f8-f218-40d9-849d-dca63be06651

import Mathlib

theorem solution {k : Type*} [Field k] {n : ℕ} (hn : 3 ≤ n) (hchar : (n : k) ≠ 0) {a b c : Polynomial k}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : IsCoprime a b) (heq : a ^ n + b ^ n = c ^ n) :
    a.natDegree = 0 ∧ b.natDegree = 0 ∧ c.natDegree = 0 :=
  Polynomial.flt hn hchar ha hb hc hab heq
