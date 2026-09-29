-- Prove2me | solution 1 for FamousTheorems.norm_le_gronwallbound_of_norm_deriv_right_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:09.423989+00:00
-- url     : https://prove2.me/submissions/2f3d0cb6-5167-4ddd-ba6f-8f67d19a27ec

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {f f' : ℝ → E} {δ K ε a b : ℝ}, 
    ContinuousOn f (Icc a b) → 
    (∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x) → 
    ‖f a‖ ≤ δ → (∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) → ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  @_root_.norm_le_gronwallBound_of_norm_deriv_right_le
