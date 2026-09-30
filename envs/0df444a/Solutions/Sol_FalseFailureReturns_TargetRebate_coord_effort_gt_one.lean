-- Prove2me | solution 1 for FalseFailureReturns.TargetRebate.coord_effort_gt_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:46:09.521389+00:00
-- url     : https://prove2.me/submissions/c506e61e-c1de-4446-bb42-8cb325c96ba3

import Definitions.Def_FalseFailureReturns_TargetRebate_Model
set_option autoImplicit false
open FalseFailureReturns.TargetRebate

theorem solution (P : Params)
    (ha : 0 < P.a) (hβ : 0 < P.β) (hM : 0 < P.Mm) (hR : 0 < P.Rr)
    (hint : P.a < (P.Mm + P.Rr) * P.β) :
    1 < coordEffort P := by
  apply Real.one_lt_rpow _ (by norm_num)
  rw [div_mul_eq_mul_div, one_lt_div ha]
  exact hint
