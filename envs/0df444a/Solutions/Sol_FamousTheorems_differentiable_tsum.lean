-- Prove2me | solution 1 for FamousTheorems.differentiable_tsum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:26:11.635925+00:00
-- url     : https://prove2.me/submissions/212af6b0-051d-4496-b854-737d67b55ddc

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} {𝕜 : Type u_2} {E : Type u_3} {F : Type u_4} [inst : NontriviallyNormedField 𝕜] 
    [IsRCLikeNormedField 𝕜] [inst_2 : NormedAddCommGroup E] [inst_3 : NormedSpace 𝕜 E] [inst_4 : NormedAddCommGroup F] 
    [CompleteSpace F] {u : α → ℝ} [inst_6 : NormedSpace 𝕜 F] {f : α → E → F} {f' : α → E → E →L[𝕜] F}, 
    Summable u → 
    (∀ (n : α) (x : E), HasFDerivAt (f n) (f' n x) x) → 
    (∀ (n : α) (x : E), ‖f' n x‖ ≤ u n) → Differentiable 𝕜 fun y => ∑' (n : α), f n y :=
  @_root_.differentiable_tsum
