-- Prove2me | solution 1 for FamousTheorems.padic_complex_alg_closed
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:28:17.806186+00:00
-- url     : https://prove2.me/submissions/a460a08e-03ef-44f3-ba68-679579e6cfc7

import Mathlib

theorem solution (p : ℕ) [Fact p.Prime] : IsAlgClosed (PadicComplex p) :=
  PadicComplex.isAlgClosed p
