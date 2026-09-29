-- Prove2me | solution 1 for FamousTheorems.pow_totient
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:59.502851+00:00
-- url     : https://prove2.me/submissions/1f26c680-4487-4938-8041-2cccbbb7260d

import Mathlib

theorem solution : ∀ {x n : ℕ}, Nat.Coprime x n → x ^ n.totient ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient
