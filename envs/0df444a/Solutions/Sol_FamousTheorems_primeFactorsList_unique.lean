-- Prove2me | solution 1 for FamousTheorems.primeFactorsList_unique
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.958327+00:00
-- url     : https://prove2.me/submissions/785c489c-bce6-47d4-9c9e-c4bac3591a9c

import Mathlib

theorem solution : ∀ {n : ℕ} {l : List ℕ}, l.prod = n → (∀ p ∈ l, Nat.Prime p) → l.Perm n.primeFactorsList :=
  Nat.primeFactorsList_unique
