-- Prove2me | solution 1 for FamousTheorems.gauss_lemma_quadratic_residues
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:10:29.653024+00:00
-- url     : https://prove2.me/submissions/5252a3c2-b7b0-4c08-80c3-aafcc5247e01

import Mathlib

theorem solution {p : ℕ} [Fact p.Prime] {a : ℤ} (hp : p ≠ 2) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a =
      (-1) ^ ((Finset.Ico 1 (p / 2).succ).filter
        (fun x : ℕ => p / 2 < ((a : ZMod p) * (x : ZMod p)).val)).card :=
  ZMod.gauss_lemma hp ha0
