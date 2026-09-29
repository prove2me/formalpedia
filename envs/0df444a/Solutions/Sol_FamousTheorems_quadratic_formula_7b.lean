-- Prove2me | solution 1 for FamousTheorems.quadratic_formula_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:15:02.812881+00:00
-- url     : https://prove2.me/submissions/8b0fbccd-8696-4f01-9e13-a3ea0bf16c45

import Mathlib

theorem solution {K : Type*} [Field K] [NeZero (2 : K)] {a b c : K} (ha : a ≠ 0) {s : K} (h : discrim a b c = s * s)
    (x : K) : a * (x * x) + b * x + c = 0 ↔ x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) :=
  quadratic_eq_zero_iff ha h x
