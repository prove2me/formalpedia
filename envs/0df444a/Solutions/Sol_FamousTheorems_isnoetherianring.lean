-- Prove2me | solution 1 for FamousTheorems.isnoetherianring
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:37.346035+00:00
-- url     : https://prove2.me/submissions/1fb56282-61d2-4324-8158-96b28384fc6d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsNoetherianRing R], 
    IsNoetherianRing (Polynomial R) :=
  @_root_.Polynomial.isNoetherianRing
