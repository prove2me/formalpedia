-- Prove2me | solution 1 for FamousTheorems.dickson_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:09.225769+00:00
-- url     : https://prove2.me/submissions/2d3cecc3-eb5b-46c2-b2f4-c0c75d5b260f

import Mathlib

theorem solution (k : ℕ) (f : ℕ → (Fin k → ℕ)) : ∃ i j, i < j ∧ f i ≤ f j :=
  wellQuasiOrdered_le f
