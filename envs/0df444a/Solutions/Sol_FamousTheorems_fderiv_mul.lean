-- Prove2me | solution 1 for FamousTheorems.fderiv_mul
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:21.521751+00:00
-- url     : https://prove2.me/submissions/d710168a-414f-47b5-ab6d-581675c6a34f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E] 
    [inst_2 : NormedSpace 𝕜 E] {x : E} {𝔸' : Type u_3} [inst_3 : NormedCommRing 𝔸'] [inst_4 : NormedAlgebra 𝕜 𝔸'] 
    {c d : E → 𝔸'}, 
    DifferentiableAt 𝕜 c x → DifferentiableAt 𝕜 d x → fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  @_root_.fderiv_mul
