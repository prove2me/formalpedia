-- Prove2me | solution 1 for FamousTheorems.hockey_stick_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:23:34.007531+00:00
-- url     : https://prove2.me/submissions/0e5f9a80-5601-4bf7-bbcb-0dccd342fdd7

import Mathlib

theorem solution (n k : ℕ) : ∑ m ∈ Finset.Icc k n, m.choose k = (n + 1).choose (k + 1) :=
  Nat.sum_Icc_choose n k
