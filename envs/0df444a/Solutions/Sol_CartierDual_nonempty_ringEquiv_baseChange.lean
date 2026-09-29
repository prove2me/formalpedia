-- Prove2me | solution 1 for CartierDual.nonempty_ringEquiv_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ad8a9dac-ccd1-5b0e-a046-41d8cb390566

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_nonempty_ringEquiv_baseChange

set_option autoImplicit false

open scoped TensorProduct

noncomputable section

namespace CartierDual
p2m_export "CartierDual" "toDual ofDual toDual_apply ext mul_apply"
namespace BaseChangeProof
p2m_open "CartierDual"

variable (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]

def E : S ⊗[R] CartierDual R A ≃ₗ[S] CartierDual S (S ⊗[R] A) :=
  (LinearEquiv.baseChange R S _ _ (CartierDual.toDual R A)) ≪≫ₗ
    (TensorProduct.isBaseChange R A S).toDualBaseChange ≪≫ₗ (CartierDual.ofDual S (S ⊗[R] A))

lemma E_tmul_apply (s r : S) (f : CartierDual R A) (a : A) :
    E R S A (s ⊗ₜ[R] f) (r ⊗ₜ[R] a) = r * (s * algebraMap R S (f a)) := by
  have hra : (r ⊗ₜ[R] a : S ⊗[R] A) = r • (TensorProduct.mk R S A 1 a) := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [hra, map_smul, smul_eq_mul]
  congr 1
  change ((TensorProduct.isBaseChange R A S).toDualBaseChange
    ((LinearEquiv.baseChange R S _ _ (CartierDual.toDual R A)) (s ⊗ₜ[R] f))) (TensorProduct.mk R S A 1 a) = _
  rw [LinearEquiv.baseChange_tmul, IsBaseChange.toDualBaseChange_tmul]
  rfl

omit [Module.Finite R A] [Module.Free R A] in

lemma mul_apply_tmul (φ ψ : CartierDual S (S ⊗[R] A)) (r : S) (a : A) :
    (φ * ψ) (r ⊗ₜ[R] a) = TensorProduct.dualDistrib S (S ⊗[R] A) (S ⊗[R] A)
      (CartierDual.toDual S (S ⊗[R] A) φ ⊗ₜ[S] CartierDual.toDual S (S ⊗[R] A) ψ)
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R S R S S S A A
        ((1 ⊗ₜ[S] r) ⊗ₜ[R] Coalgebra.comul (R := R) a)) := by
  rw [CartierDual.mul_apply]
  rfl

lemma E_map_mul (x y : S ⊗[R] CartierDual R A) : E R S A (x * y) = E R S A x * E R S A y := by

  induction x using TensorProduct.induction_on with
  | zero =>
    have h : (0 : S ⊗[R] CartierDual R A) * y = 0 := LinearMap.map_zero₂ (LinearMap.mul R (S ⊗[R] CartierDual R A)) y
    rw [h, LinearEquiv.map_zero, zero_mul]
  | add x x' hx hx' =>
    have h : (x + x') * y = x * y + x' * y := LinearMap.map_add₂ (LinearMap.mul R (S ⊗[R] CartierDual R A)) x x' y
    rw [h, LinearEquiv.map_add, LinearEquiv.map_add, add_mul, hx, hx']
  | tmul s f =>
    induction y using TensorProduct.induction_on with
    | zero =>
      have h : (s ⊗ₜ[R] f : S ⊗[R] CartierDual R A) * 0 = 0 := map_zero (LinearMap.mul R (S ⊗[R] CartierDual R A) (s ⊗ₜ[R] f))
      rw [h, LinearEquiv.map_zero, mul_zero]
    | add y y' hy hy' =>
      have h : (s ⊗ₜ[R] f : S ⊗[R] CartierDual R A) * (y + y') = s ⊗ₜ[R] f * y + s ⊗ₜ[R] f * y' :=
        map_add (LinearMap.mul R (S ⊗[R] CartierDual R A) (s ⊗ₜ[R] f)) y y'
      rw [h, LinearEquiv.map_add, LinearEquiv.map_add, mul_add, hy, hy']
    | tmul t g =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      refine CartierDual.ext fun w => ?_
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add w w' hw hw' => rw [map_add, map_add, hw, hw']
      | tmul r a =>
        rw [E_tmul_apply, mul_apply_tmul, CartierDual.mul_apply]
        generalize Coalgebra.comul (R := R) a = c
        induction c using TensorProduct.induction_on with
        | zero =>
          rw [LinearMap.map_zero, map_zero, mul_zero, mul_zero, TensorProduct.tmul_zero, LinearEquiv.map_zero,
            LinearMap.map_zero]
        | add c c' hc hc' =>
          rw [LinearMap.map_add, map_add, mul_add, mul_add, TensorProduct.tmul_add, LinearEquiv.map_add,
            LinearMap.map_add, hc, hc']
        | tmul p q =>
          rw [TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply,
            TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.dualDistrib_apply,
            CartierDual.toDual_apply, CartierDual.toDual_apply, E_tmul_apply, E_tmul_apply, map_mul]
          ring

def ringEquiv : S ⊗[R] CartierDual R A ≃+* CartierDual S (S ⊗[R] A) :=
  { (E R S A).toEquiv with
    map_mul' := E_map_mul R S A
    map_add' := fun x y => map_add (E R S A) x y }

end CartierDual.BaseChangeProof

end

open scoped TensorProduct in

theorem solution
    (R : Type) [CommRing R] (S : Type) [CommRing S] [Algebra R S]
    (A : Type) [CommRing A] [HopfAlgebra R A] [Module.Finite R A] [Module.Free R A]
    [Coalgebra.IsCocomm R A] :
    Nonempty (CartierDual S (S ⊗[R] A) ≃+* S ⊗[R] CartierDual R A) :=
  ⟨(CartierDual.BaseChangeProof.ringEquiv R S A).symm⟩

end S_CartierDual_nonempty_ringEquiv_baseChange
end P2MW
export P2MW.S_CartierDual_nonempty_ringEquiv_baseChange (solution)
