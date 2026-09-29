-- Prove2me | solution 1 for FamousTheorems.isopenmap
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:02:01.403728+00:00
-- url     : https://prove2.me/submissions/d0bd255d-264a-4f02-a794-6b86e1f07b1d

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} {𝕜' : Type u_2} [inst : NontriviallyNormedField 𝕜] 
    [inst_1 : NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} {E : Type u_3} [inst_2 : NormedAddCommGroup E] 
    [inst_3 : NormedSpace 𝕜 E] {F : Type u_4} [inst_4 : NormedAddCommGroup F] [inst_5 : NormedSpace 𝕜' F] (f : E →SL[σ] F) 
    {σ' : 𝕜' →+* 𝕜} [RingHomInvPair σ σ'] [RingHomIsometric σ] [RingHomIsometric σ'] [CompleteSpace F] [CompleteSpace E], 
    Function.Surjective ⇑f → IsOpenMap ⇑f :=
  @_root_.ContinuousLinearMap.isOpenMap
