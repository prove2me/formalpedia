-- Prove2me | solution 1 for FamousTheorems.rootset_derivative_subset_convexhull_rootset
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:10.372315+00:00
-- url     : https://prove2.me/submissions/4e2b279c-5058-4f97-802a-2a5a3c2f3d16

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {P : Polynomial ℂ}, 
    0 < P.degree → (Polynomial.derivative P).rootSet ℂ ⊆ (convexHull ℝ) (P.rootSet ℂ) :=
  @_root_.Polynomial.rootSet_derivative_subset_convexHull_rootSet
