-- Prove2me | solution 1 for FamousTheorems.convexon_of_deriv2_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.846579+00:00
-- url     : https://prove2.me/submissions/026cabda-97b0-4a07-8bbc-59fc4954c0d0

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {D : Set ℝ}, 
    Convex ℝ D → 
    ∀ {f : ℝ → ℝ}, 
    ContinuousOn f D → 
    DifferentiableOn ℝ f (interior D) → 
    DifferentiableOn ℝ (deriv f) (interior D) → (∀ x ∈ interior D, 0 ≤ deriv^[2] f x) → ConvexOn ℝ D f :=
  @_root_.convexOn_of_deriv2_nonneg
