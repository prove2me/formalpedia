-- Prove2me | solution 1 for FamousTheorems.selmer_irreducibility_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:05:28.370791+00:00
-- url     : https://prove2.me/submissions/2b52fbe4-8250-413b-bb4f-f68926fc6fd8

import Mathlib

theorem solution {n : ℕ} (hn : n ≠ 1) : Irreducible (Polynomial.X ^ n - Polynomial.X - 1 : Polynomial ℤ) :=
  Polynomial.X_pow_sub_X_sub_one_irreducible hn
