-- Prove2me | solution 1 for FamousTheorems.basis_tomatrix_mul_linearmap_tomatrix_mul_basis_tomatrix
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:38.247015+00:00
-- url     : https://prove2.me/submissions/d2835526-5442-4a33-a13c-dd30aa2d8b9b

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {ι' : Type u_2} {κ : Type u_3} 
    {κ' : Type u_4} {R : Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : Module R M] 
    {N : Type u_7} [inst_3 : AddCommMonoid N] [inst_4 : Module R N] (b : Module.Basis ι R M) (b' : Module.Basis ι' R M) 
    (c : Module.Basis κ R N) (c' : Module.Basis κ' R N) (f : M →ₗ[R] N) [inst_5 : Fintype ι'] [inst_6 : Finite κ] 
    [inst_7 : Fintype ι] [inst_8 : Fintype κ'] [inst_9 : DecidableEq ι] [inst_10 : DecidableEq ι'], 
    c.toMatrix ⇑c' * (LinearMap.toMatrix b' c') f * b'.toMatrix ⇑b = (LinearMap.toMatrix b c) f :=
  @_root_.basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
