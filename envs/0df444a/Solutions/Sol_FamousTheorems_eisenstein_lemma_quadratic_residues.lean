-- Prove2me | solution 1 for FamousTheorems.eisenstein_lemma_quadratic_residues
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:01:03.645469+00:00
-- url     : https://prove2.me/submissions/e0999763-ca5a-45fc-94ac-1cbc0d326d74

import Mathlib

theorem solution {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = (-1) ^ ∑ x ∈ Finset.Ico 1 (p / 2).succ, x * a / p :=
  ZMod.eisenstein_lemma hp ha1 ha0
