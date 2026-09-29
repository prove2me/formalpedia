-- Prove2me | solution 1 for FamousTheorems.cauchy_bound_polynomial_roots
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:39:15.383313+00:00
-- url     : https://prove2.me/submissions/b6dd6534-93e1-41ba-a318-7fe7e13140d6

import Mathlib

theorem solution {K : Type*} [NormedDivisionRing K] {p : Polynomial K} (hp : p ≠ 0) {a : K} (ha : p.IsRoot a) :
    ‖a‖₊ < p.cauchyBound :=
  Polynomial.IsRoot.norm_lt_cauchyBound hp ha
