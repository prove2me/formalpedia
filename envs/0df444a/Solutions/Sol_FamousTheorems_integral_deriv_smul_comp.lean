-- Prove2me | solution 1 for FamousTheorems.integral_deriv_smul_comp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.635806+00:00
-- url     : https://prove2.me/submissions/5aa97f47-da62-4859-b657-1c5631342bb2

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {a b : ℝ} {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {f f' : ℝ → ℝ} {g : ℝ → E}, 
    (∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) → 
    ContinuousOn f' (uIcc a b) → Continuous g → ∫ (x : ℝ) in a..b, f' x • (g ∘ f) x = ∫ (x : ℝ) in f a..f b, g x :=
  @_root_.intervalIntegral.integral_deriv_smul_comp
