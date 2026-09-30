-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.decentr_le_coord
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:46:10.11623+00:00
-- url     : https://prove2.me/submissions/75364087-fc7f-4898-a5c5-45193df82cb0

import Definitions.Def_FalseFailureReturns_TargetRebate_Model
set_option autoImplicit false
open FalseFailureReturns.TargetRebate

theorem solution (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) :
    decentrEffort P ≤ coordEffort P := by
  apply max_le
  · apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ ha.le
    nlinarith
  · apply le_of_lt (Real.one_lt_rpow _ (by norm_num))
    rw [div_mul_eq_mul_div, one_lt_div ha]
    exact hint
