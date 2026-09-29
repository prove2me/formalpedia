-- Prove2me | solution 1 for FamousTheorems.jacobi_quadratic_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:59:29.593836+00:00
-- url     : https://prove2.me/submissions/e0939434-237b-4df1-bb4b-e2e246425101

import Mathlib

theorem solution {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    jacobiSym (a : ℤ) b = (-1) ^ (a / 2 * (b / 2)) * jacobiSym (b : ℤ) a :=
  jacobiSym.quadratic_reciprocity ha hb
