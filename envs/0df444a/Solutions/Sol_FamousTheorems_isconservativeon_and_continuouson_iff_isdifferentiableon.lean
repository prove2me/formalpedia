-- Prove2me | solution 1 for FamousTheorems.isconservativeon_and_continuouson_iff_isdifferentiableon
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:07.41689+00:00
-- url     : https://prove2.me/submissions/b64e059e-1529-4d2f-b730-7797983128d6

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℂ E] {f : ℂ → E} [CompleteSpace E] {U : Set ℂ}, 
    IsOpen U → (Complex.IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn ℂ f U) :=
  @_root_.Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn
