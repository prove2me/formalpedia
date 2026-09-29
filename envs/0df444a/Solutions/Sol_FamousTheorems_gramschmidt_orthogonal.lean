-- Prove2me | solution 1 for FamousTheorems.gramschmidt_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:46.562398+00:00
-- url     : https://prove2.me/submissions/9b0d6dae-baaf-4e0b-ba99-314afe73aa24

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (𝕜 : Type u_1) {E : Type u_2} [inst : RCLike 𝕜] 
    [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] {ι : Type u_3} [inst_3 : LinearOrder ι] 
    [inst_4 : LocallyFiniteOrderBot ι] [inst_5 : WellFoundedLT ι] (f : ι → E) {a b : ι}, 
    a ≠ b → inner 𝕜 (InnerProductSpace.gramSchmidt 𝕜 f a) (InnerProductSpace.gramSchmidt 𝕜 f b) = 0 :=
  @_root_.InnerProductSpace.gramSchmidt_orthogonal
