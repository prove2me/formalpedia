-- Prove2me | solution 1 for FamousTheorems.infinitely_many_fermat_pseudoprimes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:40:55.555048+00:00
-- url     : https://prove2.me/submissions/13878cbe-fee0-420d-a7b0-b51d8f82ae5f

import Mathlib

theorem solution {b : ℕ} (hb : 1 ≤ b) (m : ℕ) : ∃ n : ℕ, n.FermatPsp b ∧ m ≤ n :=
  Nat.exists_infinite_pseudoprimes hb m
