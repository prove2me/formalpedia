-- Prove2me | solution 1 for FamousTheorems.subgroupisfreeofisfree
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:05.260192+00:00
-- url     : https://prove2.me/submissions/539620f5-44f5-4321-ada9-1cb4aeec5ae3

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G] (H : Subgroup G), IsFreeGroup ↥H :=
  @_root_.subgroupIsFreeOfIsFree
