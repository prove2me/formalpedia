-- Prove2me | solution 1 for FamousTheorems.wilsons_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.803098+00:00
-- url     : https://prove2.me/submissions/55c85e8e-3c62-4bdb-bee8-8c45637d1344

import Mathlib

theorem solution : ∀ (p : ℕ) [Fact (Nat.Prime p)], (((p - 1).factorial : ℕ) : ZMod p) = -1 :=
  ZMod.wilsons_lemma
