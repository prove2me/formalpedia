-- Prove2me | solution 2 for FamousTheorems.number_field_product_formula
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:36:36.157229+00:00
-- url     : https://prove2.me/submissions/4a2af816-fe5d-4253-8467-1f684b2ae22e

import Mathlib

theorem solution {K : Type*} [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : NumberField.FinitePlace K, w x = 1 := by
  exact NumberField.prod_abs_eq_one hx
