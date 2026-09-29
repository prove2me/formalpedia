-- Prove2me | solution 1 for FamousTheorems.catalan_number_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:16:08.012091+00:00
-- url     : https://prove2.me/submissions/e0d59ad4-d941-44f8-b702-d225603af2cc

import Mathlib

theorem solution (n : ℕ) : (n + 1) * catalan n = n.centralBinom ∧ catalan n = n.centralBinom / (n + 1) :=
  ⟨succ_mul_catalan_eq_centralBinom n, catalan_eq_centralBinom_div n⟩
