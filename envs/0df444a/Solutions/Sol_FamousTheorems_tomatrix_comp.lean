-- Prove2me | solution 1 for FamousTheorems.tomatrix_comp
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:38.17118+00:00
-- url     : https://prove2.me/submissions/c85623b2-c950-4b54-a42b-7078d05e6725

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R₁ : Type u_1} {M₁ : Type u_2} [inst : CommSemiring R₁] 
    [inst_1 : AddCommMonoid M₁] [inst_2 : Module R₁ M₁] {n : Type u_3} {o : Type u_4} [inst_3 : Fintype n] 
    [inst_4 : Fintype o] [inst_5 : DecidableEq n] (b : Module.Basis n R₁ M₁) {M₂' : Type u_5} [inst_6 : AddCommMonoid M₂'] 
    [inst_7 : Module R₁ M₂'] (c : Module.Basis o R₁ M₂') [inst_8 : DecidableEq o] (B : LinearMap.BilinForm R₁ M₁) 
    (l r : M₂' →ₗ[R₁] M₁), 
    (LinearMap.BilinForm.toMatrix c) (B.comp l r) = 
    ((LinearMap.toMatrix c b) l).transpose * (LinearMap.BilinForm.toMatrix b) B * (LinearMap.toMatrix c b) r :=
  @_root_.LinearMap.BilinForm.toMatrix_comp
