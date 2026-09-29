-- Prove2me | solution 1 for FamousTheorems.two_pi_i_inv_smul_circleintegral_sub_inv_smul_of_differentiable_on_off_countable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:12.110877+00:00
-- url     : https://prove2.me/submissions/a67856f2-4d18-494c-8a15-5671d7dd1d4d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} 
    [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {R : ℝ} {c w : ℂ} {f : ℂ → E} {s : Set ℂ}, 
    s.Countable → 
    w ∈ Metric.ball c R → 
    ContinuousOn f (Metric.closedBall c R) → 
    (∀ x ∈ Metric.ball c R \ s, DifferentiableAt ℂ f x) → 
    (2 * ↑Real.pi * Complex.I)⁻¹ • ∮ (z : ℂ) in C(c, R), (z - w)⁻¹ • f z = f w :=
  @_root_.Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
