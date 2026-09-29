-- Prove2me | solution 1 for FamousTheorems.lucas_primality_test
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:13:46.170395+00:00
-- url     : https://prove2.me/submissions/1663256f-de4a-4950-b56c-6222236e38ea

import Mathlib

theorem solution (p : ℕ) (a : ZMod p) (ha : a ^ (p - 1) = 1)
    (hd : ∀ q : ℕ, q.Prime → q ∣ p - 1 → a ^ ((p - 1) / q) ≠ 1) : p.Prime :=
  lucas_primality p a ha hd
