-- Prove2me | solution 1 for FamousTheorems.second_derivative_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:00.511203+00:00
-- url     : https://prove2.me/submissions/111c2d47-780a-41ef-8225-3bbb67bd3a46

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} {F : Type u_3} 
    [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E] [inst_3 : NormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] 
    {f : E → F} [IsRCLikeNormedField 𝕜] {f' : E → E →L[𝕜] F} {f'' : E →L[𝕜] E →L[𝕜] F} {x : E}, 
    (∀ (y : E), HasFDerivAt f (f' y) y) → HasFDerivAt f' f'' x → ∀ (v w : E), (f'' v) w = (f'' w) v :=
  @_root_.second_derivative_symmetric
