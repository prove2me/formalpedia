-- Prove2me | solution 1 for Coalgebra.eq_lTensor_comul_sub_tmul_one_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6e040e38-dc08-55f9-9375-a2c32e3ac9b0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace COFREEH1

variable {R : Type*} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
  {N : Type*} [AddCommGroup N] [Module R N]

noncomputable def M' : (N ⊗[R] C) ⊗[R] C →ₗ[R] N ⊗[R] C :=
  _root_.TensorProduct.map (_root_.TensorProduct.rid R N ∘ₗ LinearMap.lTensor N Coalgebra.counit) LinearMap.id

theorem M'_tmul (x : N ⊗[R] C) (c : C) :
    M' (R := R) (x ⊗ₜ[R] c) = (_root_.TensorProduct.rid R N (LinearMap.lTensor N Coalgebra.counit x)) ⊗ₜ[R] c := rfl

theorem M'_tmul_tmul (n : N) (c c' : C) :
    M' (R := R) ((n ⊗ₜ[R] c) ⊗ₜ[R] c') = (Coalgebra.counit (R := R) c • n) ⊗ₜ[R] c' := by
  rw [M'_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]

noncomputable def Phi : ((N ⊗[R] C) ⊗[R] C) ⊗[R] C →ₗ[R] (N ⊗[R] C) ⊗[R] C :=
  LinearMap.rTensor C (M' (R := R) (C := C) (N := N))

theorem Phi_tmul (y : (N ⊗[R] C) ⊗[R] C) (c : C) : Phi (R := R) (y ⊗ₜ[R] c) = M' y ⊗ₜ[R] c := rfl

theorem Phi_A (e : (N ⊗[R] C) ⊗[R] C) :
    Phi ((_root_.TensorProduct.assoc R (N ⊗[R] C) C C).symm (LinearMap.lTensor (N ⊗[R] C) Coalgebra.comul e)) =
      (_root_.TensorProduct.assoc R N C C).symm (LinearMap.lTensor N Coalgebra.comul (M' e)) := by
  induction e using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c' =>
    rw [LinearMap.lTensor_tmul, M'_tmul, LinearMap.lTensor_tmul]
    generalize Coalgebra.comul (R := R) c' = w
    induction w using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | tmul u v =>
      rw [TensorProduct.assoc_symm_tmul, TensorProduct.assoc_symm_tmul, Phi_tmul, M'_tmul]
    | add w₁ w₂ h₁ h₂ => rw [TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, map_add, map_add, h₁, h₂]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Phi_B (e : (N ⊗[R] C) ⊗[R] C) :
    Phi (_root_.TensorProduct.map (_root_.TensorProduct.assoc R N C C).symm.toLinearMap LinearMap.id
      (LinearMap.rTensor C (LinearMap.lTensor N Coalgebra.comul) e)) = e := by
  classical
  induction e using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x c' =>
    rw [LinearMap.rTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply, Phi_tmul]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul n c =>
      rw [LinearMap.lTensor_tmul]
      let 𝓡 := Coalgebra.Repr.arbitrary R c
      conv_lhs => rw [← 𝓡.eq]
      rw [TensorProduct.tmul_sum, map_sum, map_sum]
      simp only [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul, M'_tmul_tmul]
      rw [show (∑ x ∈ 𝓡.index, (Coalgebra.counit (R := R) (𝓡.left x) • n) ⊗ₜ[R] 𝓡.right x) =
          ∑ x ∈ 𝓡.index, n ⊗ₜ[R] (Coalgebra.counit (R := R) (𝓡.left x) • 𝓡.right x) from
          Finset.sum_congr rfl fun i _ => by rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul],
        ← TensorProduct.tmul_sum, Coalgebra.sum_counit_smul 𝓡]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem Phi_tmul_c (e : (N ⊗[R] C) ⊗[R] C) (c₀ : C) : Phi (R := R) (e ⊗ₜ[R] c₀) = M' e ⊗ₜ[R] c₀ := rfl

end COFREEH1

namespace COFREEH1

variable {R : Type} [CommRing R] {L : Type} [CommRing L] [Bialgebra R L] {N : Type} [AddCommGroup N] [Module R N]

theorem Phi_B' (e : (N ⊗[R] L) ⊗[R] L) :
    Phi (((_root_.TensorProduct.assoc R N L L).symm.toLinearMap.rTensor L)
      (((Coalgebra.comul (R := R) (A := L)).lTensor N).rTensor L e)) = e :=
  Phi_B e

theorem m_eq (e : (N ⊗[R] L) ⊗[R] L) :
    ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e)) =
      M' e := by
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  rfl

end COFREEH1

open COFREEH1 in
theorem solution
    {R : Type} [CommRing R] {L : Type} [CommRing L] [Bialgebra R L]
    {N : Type} [AddCommGroup N] [Module R N]
    (e : (N ⊗[R] L) ⊗[R] L)
    (he : (_root_.TensorProduct.assoc R (N ⊗[R] L) L L).symm ((Coalgebra.comul (R := R) (A := L)).lTensor (N ⊗[R] L) e) =
      ((_root_.TensorProduct.assoc R N L L).symm.toLinearMap.rTensor L)
          (((Coalgebra.comul (R := R) (A := L)).lTensor N).rTensor L e) +
        e ⊗ₜ[R] (1 : L)) :
    e = (_root_.TensorProduct.assoc R N L L).symm
          ((Coalgebra.comul (R := R) (A := L)).lTensor N
            ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e))) -
        ((_root_.TensorProduct.rid R N).toLinearMap.rTensor L
              (((Coalgebra.counit (R := R) (A := L)).lTensor N).rTensor L e)) ⊗ₜ[R] (1 : L) := by
  rw [COFREEH1.m_eq]
  have h := congrArg (COFREEH1.Phi (R := R) (C := L) (N := N)) he
  rw [map_add, COFREEH1.Phi_A, COFREEH1.Phi_B', COFREEH1.Phi_tmul_c] at h
  exact eq_sub_of_add_eq h.symm

end S_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle
end P2MW
export P2MW.S_Coalgebra_eq_lTensor_comul_sub_tmul_one_of_cocycle (solution)
