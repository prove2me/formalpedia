-- Prove2me | solution 1 for FamousTheorems.euclid_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:28:16.878841+00:00
-- url     : https://prove2.me/submissions/7289951f-d43e-41fb-9d01-b76a5abcf842

import Mathlib

theorem solution {p m n : ℕ} (hp : p.Prime) : p ∣ m * n ↔ p ∣ m ∨ p ∣ n :=
  hp.dvd_mul
