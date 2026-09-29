-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_negative_integers_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:06:53.02046+00:00
-- url     : https://prove2.me/submissions/a379d673-dc2d-4edc-9602-ecbaf8364e73

import Mathlib

theorem solution (k : ℕ) : riemannZeta (-(k : ℂ)) = (-1) ^ k * (bernoulli (k + 1) : ℂ) / (k + 1) :=
  riemannZeta_neg_nat_eq_bernoulli k
