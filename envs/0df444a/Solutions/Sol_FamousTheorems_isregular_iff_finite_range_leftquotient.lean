-- Prove2me | solution 1 for FamousTheorems.isregular_iff_finite_range_leftquotient
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:28.086104+00:00
-- url     : https://prove2.me/submissions/86f77fe3-e43d-430a-8c1d-974a3fe26c43

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {L : Language α}, 
    L.IsRegular ↔ (range L.leftQuotient).Finite :=
  @_root_.Language.isRegular_iff_finite_range_leftQuotient
