-- Prove2me | solution 1 for FamousTheorems.integral_mul_deriv_eq_deriv_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.920993+00:00
-- url     : https://prove2.me/submissions/e1509ada-f75e-4f04-b7bc-59c0b9c62b9d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {a b : ℝ} {A : Type u_1} [inst : NormedRing A] 
    [inst_1 : NormedAlgebra ℝ A] [CompleteSpace A] {u v u' v' : ℝ → A}, 
    (∀ x ∈ uIcc a b, HasDerivAt u (u' x) x) → 
    (∀ x ∈ uIcc a b, HasDerivAt v (v' x) x) → 
    IntervalIntegrable u' MeasureTheory.volume a b → 
    IntervalIntegrable v' MeasureTheory.volume a b → 
    ∫ (x : ℝ) in a..b, u x * v' x = u b * v b - u a * v a - ∫ (x : ℝ) in a..b, u' x * v x :=
  @_root_.intervalIntegral.integral_mul_deriv_eq_deriv_mul
