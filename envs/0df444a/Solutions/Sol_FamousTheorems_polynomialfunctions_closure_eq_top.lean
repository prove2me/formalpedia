-- Prove2me | solution 1 for FamousTheorems.polynomialfunctions_closure_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.456179+00:00
-- url     : https://prove2.me/submissions/4fedbaee-1144-4588-a624-ee8a611fd566

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (a b : ℝ), (polynomialFunctions (Icc a b)).topologicalClosure = ⊤ :=
  @_root_.polynomialFunctions_closure_eq_top
