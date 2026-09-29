-- Prove2me | solution 1 for FamousTheorems.number_field_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:20:16.992924+00:00
-- url     : https://prove2.me/submissions/d24290e1-131b-406d-9672-475f0dedebbf

import Mathlib

theorem solution {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : NumberField.FinitePlace K, w x = 1 :=
  NumberField.prod_abs_eq_one hx
