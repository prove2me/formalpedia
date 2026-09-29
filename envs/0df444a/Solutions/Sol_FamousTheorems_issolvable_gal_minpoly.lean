-- Prove2me | solution 1 for FamousTheorems.issolvable_gal_minpoly
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:42.016366+00:00
-- url     : https://prove2.me/submissions/70de49b0-8527-46ba-9d60-943f6701b933

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {F : Type u_1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] 
    {x : E}, x ∈ solvableByRad F E → Group.IsSolvable (minpoly F x).Gal :=
  @_root_.isSolvable_gal_minpoly
