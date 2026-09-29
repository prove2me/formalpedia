-- Prove2me | solution 1 for FamousTheorems.cyclotomic_polynomial_irreducible_rat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:07:36.440392+00:00
-- url     : https://prove2.me/submissions/f19c9a37-ec59-45b1-a829-41bd57e7385a

import Mathlib

theorem solution {n : ℕ} (hn : 0 < n) : Irreducible (Polynomial.cyclotomic n ℚ) :=
  Polynomial.cyclotomic.irreducible_rat hn
