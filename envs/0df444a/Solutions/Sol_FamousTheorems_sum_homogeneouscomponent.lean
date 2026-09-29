-- Prove2me | solution 1 for FamousTheorems.sum_homogeneouscomponent
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:47.026515+00:00
-- url     : https://prove2.me/submissions/ca181116-70c6-4331-883d-0cdcb739b14f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (φ : MvPolynomial σ R), 
    ∑ i ∈ Finset.range (φ.totalDegree + 1), (MvPolynomial.homogeneousComponent i) φ = φ :=
  @_root_.MvPolynomial.sum_homogeneousComponent
