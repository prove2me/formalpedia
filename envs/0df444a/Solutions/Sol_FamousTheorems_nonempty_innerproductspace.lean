-- Prove2me | solution 1 for FamousTheorems.nonempty_innerproductspace
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:30.430436+00:00
-- url     : https://prove2.me/submissions/b4bfc674-fff8-463c-aef5-3b0d0e6ddd7f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (𝕜 : Type u_1) [inst : RCLike 𝕜] (E : Type u_2) [inst_1 : NormedAddCommGroup E] 
    [NormedSpace 𝕜 E] [InnerProductSpaceable E], Nonempty (InnerProductSpace 𝕜 E) :=
  @_root_.nonempty_innerProductSpace
