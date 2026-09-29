-- Prove2me | solution 1 for FamousTheorems.totient_multiplicative_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:16:29.21923+00:00
-- url     : https://prove2.me/submissions/a4f3d1a5-0762-4ee2-9486-199bf9512467

import Mathlib

theorem solution {m n : ℕ} (h : Nat.Coprime m n) : Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  Nat.totient_mul h
