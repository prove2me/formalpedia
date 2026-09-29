-- Prove2me | solution 1 for FamousTheorems.triple_product_eq_det
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:38.174589+00:00
-- url     : https://prove2.me/submissions/9b8f2e40-a01f-4499-98a1-9efbcb231d3b

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R : Type u_1} [inst : CommRing R] (u v w : Fin 3 → R), 
    u ⬝ᵥ (crossProduct v) w = Matrix.det ![u, v, w] :=
  @_root_.triple_product_eq_det
