-- Prove2me | solution 1 for FamousTheorems.sum_lt_prod
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:12:48.242112+00:00
-- url     : https://prove2.me/submissions/cafdd098-8592-446e-9020-793c9835849f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} (f g : ι → Cardinal.{u_2}), 
    (∀ (i : ι), f i < g i) → Cardinal.sum f < Cardinal.prod g :=
  @_root_.Cardinal.sum_lt_prod
