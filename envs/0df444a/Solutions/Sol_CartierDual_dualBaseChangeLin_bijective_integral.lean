-- Prove2me | solution 1 for CartierDual.dualBaseChangeLin_bijective_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/92d87d05-7de8-586a-b151-db3a3e095e5e

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral

set_option autoImplicit false

open scoped TensorProduct

section P11_CDBC_INT

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct
open Coalgebra

namespace P2MQ2CDBC

section ReadOff
variable {R : Type*} [CommRing R] {X : Type*} [CommRing X] [Bialgebra R X]

theorem cd_add_apply (φ ψ : CartierDual R X) (x : X) : (φ + ψ) x = φ x + ψ x := by
  rw [← CartierDual.toDual_apply (φ + ψ), map_add, LinearMap.add_apply, CartierDual.toDual_apply,
    CartierDual.toDual_apply]

theorem cd_zero_apply (x : X) : (0 : CartierDual R X) x = 0 := by
  rw [← CartierDual.toDual_apply (0 : CartierDual R X), map_zero, LinearMap.zero_apply]

theorem cd_smul_apply (c : R) (φ : CartierDual R X) (x : X) : (c • φ) x = c * φ x := by
  rw [← CartierDual.toDual_apply (c • φ), LinearEquiv.map_smul, LinearMap.smul_apply, smul_eq_mul,
    CartierDual.toDual_apply]

theorem cd_one_apply (x : X) : (1 : CartierDual R X) x = counit (R := R) x := by
  rw [CartierDual.one_def, CartierDual.ofDual_apply]

theorem cd_sum_apply {ι : Type*} (s : Finset ι) (φ : ι → CartierDual R X) (x : X) :
    (∑ i ∈ s, φ i) x = ∑ i ∈ s, φ i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, cd_zero_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cd_add_apply, ih]

theorem cd_mul_apply_repr [Module.Finite R X] [Module.Free R X] (φ ψ : CartierDual R X) {x : X} {ι : Type*} (rr : Coalgebra.Repr R x ι) :
    (φ * ψ) x = ∑ i ∈ rr.index, φ (rr.left i) * ψ (rr.right i) := by
  rw [CartierDual.mul_apply, ← rr.eq, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply]

theorem cd_comul_repr_pairing [Module.Finite R X] [Module.Free R X] (φ : CartierDual R X)
    {ι : Type*} (rr : Coalgebra.Repr R φ ι) (a b : X) :
    ∑ i ∈ rr.index, rr.left i a * rr.right i b = φ (a * b) := by
  rw [← CartierDual.comul_pairing φ a b, ← rr.eq, map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
  rfl

end ReadOff

universe u v w
variable (O : Type u) [CommRing O] (F : Type v) [CommRing F] [Algebra O F]
variable (A : Type w) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A]

noncomputable scoped instance instBialgebraTensorCD : Bialgebra F (F ⊗[O] CartierDual O A) :=
  TensorProduct.instBialgebra O F F (CartierDual O A)
noncomputable scoped instance instModuleFiniteTensorCD : Module.Finite F (F ⊗[O] CartierDual O A) :=
  Module.Finite.base_change O F (CartierDual O A)

variable {O F A}

omit [Module.Finite O A] [Module.Free O A] in
theorem bcLin_one : CartierDual.dualBaseChangeLin O F A 1 = 1 := by
  refine CartierDual.ext fun x => ?_
  rw [Algebra.TensorProduct.one_def, cd_one_apply]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c a =>
    rw [CartierDual.dualBaseChangeLin_tmul_tmul, one_mul, cd_one_apply, TensorProduct.counit_tmul, CommSemiring.counit_apply, Algebra.smul_def,
      mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem bcLin_mul_tmul (c d : F) (φ ψ : CartierDual O A) :
    CartierDual.dualBaseChangeLin O F A ((c ⊗ₜ[O] φ) * (d ⊗ₜ[O] ψ)) = CartierDual.dualBaseChangeLin O F A (c ⊗ₜ[O] φ) * CartierDual.dualBaseChangeLin O F A (d ⊗ₜ[O] ψ) := by
  refine CartierDual.ext fun x => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul]
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c' a =>
    let rr := Coalgebra.Repr.arbitrary O a

    rw [CartierDual.dualBaseChangeLin_tmul_tmul, cd_mul_apply_repr φ ψ rr, map_sum, Finset.mul_sum]

    have hco : comul (R := F) (c' ⊗ₜ[O] a)
        = ∑ i ∈ rr.index, ((1 : F) ⊗ₜ[O] rr.left i) ⊗ₜ[F] (c' ⊗ₜ[O] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    rw [CartierDual.mul_apply, hco, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply, CartierDual.dualBaseChangeLin_tmul_tmul,
      CartierDual.dualBaseChangeLin_tmul_tmul, map_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem bcLin_mul (x y : F ⊗[O] CartierDual O A) : CartierDual.dualBaseChangeLin O F A (x * y) = CartierDual.dualBaseChangeLin O F A x * CartierDual.dualBaseChangeLin O F A y := by

  induction x using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, zero_mul (CartierDual.dualBaseChangeLin O F A y)]
    exact (congrArg (CartierDual.dualBaseChangeLin O F A) (MulZeroClass.zero_mul y)).trans (map_zero _)
  | tmul c φ =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, mul_zero (CartierDual.dualBaseChangeLin O F A (c ⊗ₜ[O] φ))]
      exact (congrArg (CartierDual.dualBaseChangeLin O F A) (MulZeroClass.mul_zero (c ⊗ₜ[O] φ))).trans (map_zero _)
    | tmul d ψ => exact bcLin_mul_tmul c d φ ψ
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, mul_add (CartierDual.dualBaseChangeLin O F A (c ⊗ₜ[O] φ)) (CartierDual.dualBaseChangeLin O F A y₁)
        (CartierDual.dualBaseChangeLin O F A y₂), ← h₁, ← h₂, ← map_add]
      exact congrArg (CartierDual.dualBaseChangeLin O F A) (Distrib.left_distrib (c ⊗ₜ[O] φ) y₁ y₂)
  | add x₁ x₂ h₁ h₂ =>
    rw [map_add, add_mul (CartierDual.dualBaseChangeLin O F A x₁) (CartierDual.dualBaseChangeLin O F A x₂)
      (CartierDual.dualBaseChangeLin O F A y), ← h₁, ← h₂, ← map_add]
    exact congrArg (CartierDual.dualBaseChangeLin O F A) (Distrib.right_distrib x₁ x₂ y)

variable (O F A) in

noncomputable def bcAlgHom : F ⊗[O] CartierDual O A →ₐ[F] CartierDual F (F ⊗[O] A) :=
  AlgHom.ofLinearMap (CartierDual.dualBaseChangeLin O F A) bcLin_one bcLin_mul

@[scoped simp] theorem bcAlgHom_apply (x : F ⊗[O] CartierDual O A) : bcAlgHom O F A x = CartierDual.dualBaseChangeLin O F A x := rfl

theorem bcLin_bijective : Function.Bijective (CartierDual.dualBaseChangeLin O F A) := by
  classical
  let b := Module.Free.chooseBasis O A
  let β : Module.Basis (Module.Free.ChooseBasisIndex O A) O (CartierDual O A) :=
    b.dualBasis.map (CartierDual.toDual O A).symm
  let B1 : Module.Basis (Module.Free.ChooseBasisIndex O A) F (F ⊗[O] CartierDual O A) := Algebra.TensorProduct.basis F β
  let bF : Module.Basis (Module.Free.ChooseBasisIndex O A) F (F ⊗[O] A) := Algebra.TensorProduct.basis F b
  let B2 : Module.Basis (Module.Free.ChooseBasisIndex O A) F (CartierDual F (F ⊗[O] A)) :=
    bF.dualBasis.map (CartierDual.toDual F (F ⊗[O] A)).symm
  have hβ : ∀ i j, β i (b j) = if j = i then 1 else 0 := by
    intro i j
    show ((CartierDual.toDual O A).symm (b.dualBasis i)) (b j) = _
    rw [← CartierDual.toDual_apply ((CartierDual.toDual O A).symm (b.dualBasis i)) (b j), LinearEquiv.apply_symm_apply,
      Module.Basis.dualBasis_apply_self]
  have hB2 : ∀ i j, B2 i (bF j) = if j = i then 1 else 0 := by
    intro i j
    show ((CartierDual.toDual F (F ⊗[O] A)).symm (bF.dualBasis i)) (bF j) = _
    rw [← CartierDual.toDual_apply ((CartierDual.toDual F (F ⊗[O] A)).symm (bF.dualBasis i)) (bF j),
      LinearEquiv.apply_symm_apply, Module.Basis.dualBasis_apply_self]
  have key : ∀ i, CartierDual.dualBaseChangeLin O F A (B1 i) = B2 i := by
    intro i
    apply (CartierDual.toDual F (F ⊗[O] A)).injective
    apply bF.ext
    intro j
    rw [CartierDual.toDual_apply, CartierDual.toDual_apply, hB2,
      show B1 i = (1 : F) ⊗ₜ[O] β i from Algebra.TensorProduct.basis_apply β i,
      show bF j = (1 : F) ⊗ₜ[O] b j from Algebra.TensorProduct.basis_apply b j,
      CartierDual.dualBaseChangeLin_tmul_tmul, one_mul, one_mul, hβ]
    split_ifs <;> simp
  have hEq : CartierDual.dualBaseChangeLin O F A = (B1.equiv B2 (Equiv.refl _)).toLinearMap :=
    B1.ext fun i => by rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply, key]
  rw [hEq]
  exact (B1.equiv B2 (Equiv.refl _)).bijective

variable (O F A) in

noncomputable def bc : F ⊗[O] CartierDual O A ≃ₐ[F] CartierDual F (F ⊗[O] A) :=
  AlgEquiv.ofBijective (bcAlgHom O F A) bcLin_bijective

theorem bc_apply (x : F ⊗[O] CartierDual O A) : bc O F A x = CartierDual.dualBaseChangeLin O F A x := rfl

theorem bc_tmul_tmul (c : F) (φ : CartierDual O A) (c' : F) (a : A) :
    bc O F A (c ⊗ₜ[O] φ) (c' ⊗ₜ[O] a) = c * c' * algebraMap O F (φ a) :=
  CartierDual.dualBaseChangeLin_tmul_tmul c φ c' a

theorem counit_bc (w : F ⊗[O] CartierDual O A) : counit (R := F) (bc O F A w) = counit (R := F) w := by
  rw [bc_apply, CartierDual.counit_apply]
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, cd_zero_apply]
  | tmul c φ =>
    rw [Algebra.TensorProduct.one_def, CartierDual.dualBaseChangeLin_tmul_tmul, TensorProduct.counit_tmul, CommSemiring.counit_apply,
      CartierDual.counit_apply, Algebra.smul_def, mul_one, mul_comm]
  | add x y hx hy => rw [map_add, map_add, cd_add_apply, hx, hy]

set_option maxHeartbeats 3200000 in

theorem pairingAux_sum {ι : Type*} (s : Finset ι)
    (t : ι → (F ⊗[O] CartierDual O A) ⊗[F] (F ⊗[O] CartierDual O A)) (x y : F ⊗[O] A) :
    TensorProduct.dualDistrib F (F ⊗[O] A) (F ⊗[O] A)
      (TensorProduct.map (CartierDual.toDual F (F ⊗[O] A)).toLinearMap (CartierDual.toDual F (F ⊗[O] A)).toLinearMap
        (TensorProduct.map (bc O F A).toLinearMap (bc O F A).toLinearMap (∑ i ∈ s, t i))) (x ⊗ₜ[F] y)
      = ∑ i ∈ s, TensorProduct.dualDistrib F (F ⊗[O] A) (F ⊗[O] A)
          (TensorProduct.map (CartierDual.toDual F (F ⊗[O] A)).toLinearMap (CartierDual.toDual F (F ⊗[O] A)).toLinearMap
            (TensorProduct.map (bc O F A).toLinearMap (bc O F A).toLinearMap (t i))) (x ⊗ₜ[F] y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    repeat erw [LinearMap.map_zero]
    try rw [LinearMap.zero_apply]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    erw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply]

set_option maxHeartbeats 6400000 in

theorem map_bc_comul_pairing (w : F ⊗[O] CartierDual O A) (x y : F ⊗[O] A) :
    TensorProduct.dualDistrib F (F ⊗[O] A) (F ⊗[O] A)
      (TensorProduct.map (CartierDual.toDual F (F ⊗[O] A)).toLinearMap (CartierDual.toDual F (F ⊗[O] A)).toLinearMap
        (TensorProduct.map (bc O F A).toLinearMap (bc O F A).toLinearMap (comul (R := F) w))) (x ⊗ₜ[F] y)
      = bc O F A w (x * y) := by
  induction w using TensorProduct.induction_on with
  | zero =>
    have h0 : comul (R := F) (0 : F ⊗[O] CartierDual O A)
        = ∑ i ∈ (∅ : Finset ℕ), (0 : (F ⊗[O] CartierDual O A) ⊗[F] (F ⊗[O] CartierDual O A)) := by
      rw [Finset.sum_empty]; exact LinearMap.map_zero _
    erw [h0, pairingAux_sum]
    try rw [Finset.sum_empty, map_zero, cd_zero_apply]
  | tmul c φ =>
    let rr := Coalgebra.Repr.arbitrary O φ
    have hco : comul (R := F) (c ⊗ₜ[O] φ)
        = ∑ i ∈ rr.index, ((1 : F) ⊗ₜ[O] rr.left i) ⊗ₜ[F] (c ⊗ₜ[O] rr.right i) := by
      rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← rr.eq, TensorProduct.tmul_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
    have hterm : ∀ i (x y : F ⊗[O] A),
        TensorProduct.dualDistrib F (F ⊗[O] A) (F ⊗[O] A)
          (TensorProduct.map (CartierDual.toDual F (F ⊗[O] A)).toLinearMap (CartierDual.toDual F (F ⊗[O] A)).toLinearMap
            (TensorProduct.map (bc O F A).toLinearMap (bc O F A).toLinearMap
              (((1 : F) ⊗ₜ[O] rr.left i) ⊗ₜ[F] (c ⊗ₜ[O] rr.right i)))) (x ⊗ₜ[F] y)
          = bc O F A ((1 : F) ⊗ₜ[O] rr.left i) x * bc O F A (c ⊗ₜ[O] rr.right i) y := by
      intro i x y
      simp only [TensorProduct.map_tmul, AlgEquiv.toLinearMap_apply]
      erw [TensorProduct.dualDistrib_apply]
      rfl
    erw [hco, pairingAux_sum]
    trans ∑ i ∈ rr.index, bc O F A ((1 : F) ⊗ₜ[O] rr.left i) x * bc O F A (c ⊗ₜ[O] rr.right i) y
    · exact Finset.sum_congr rfl fun i _ => hterm i x y

    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, zero_mul, Finset.sum_const_zero]
    | tmul c₁ a =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, mul_zero, Finset.sum_const_zero]
      | tmul c₂ a' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, bc_tmul_tmul, ← cd_comul_repr_pairing φ rr a a', map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [bc_tmul_tmul, bc_tmul_tmul, map_mul]
        ring
      | add y₁ y₂ h₁ h₂ =>
        rw [mul_add, map_add, ← h₁, ← h₂, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_add, mul_add]
    | add x₁ x₂ h₁ h₂ =>
      rw [add_mul, map_add, ← h₁, ← h₂, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_add, add_mul]
  | add w₁ w₂ h₁ h₂ =>
    erw [LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.map_add, LinearMap.add_apply, map_add,
      cd_add_apply, h₁, h₂]

theorem map_bc_comul (w : F ⊗[O] CartierDual O A) :
    TensorProduct.map (bc O F A).toLinearMap (bc O F A).toLinearMap (comul (R := F) w) = comul (R := F) (bc O F A w) :=
  CartierDual.tmul_eq_of_pairing_eq fun x y => by rw [map_bc_comul_pairing, CartierDual.comul_pairing]

omit [Module.Finite O A] [Module.Free O A] in

theorem antipode_baseChange_tmul (c : F) (a : A) :
    HopfAlgebraStruct.antipode (R := F) (c ⊗ₜ[O] a) = c ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) a := by
  rfl

theorem bc_one_tmul_antipode (g : CartierDual O A) (x : F ⊗[O] A) :
    bc O F A ((1 : F) ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
      = bc O F A ((1 : F) ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := F) x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul c a => rw [antipode_baseChange_tmul, bc_tmul_tmul, bc_tmul_tmul, CartierDual.antipode_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem bc_one_tmul_antipode_tmul (g : CartierDual O A) (c : F) (a : A) :
    bc O F A ((1 : F) ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) (c ⊗ₜ[O] a)
      = c * algebraMap O F (g (HopfAlgebraStruct.antipode (R := O) a)) := by
  rw [bc_tmul_tmul, one_mul, CartierDual.antipode_apply]

end P2MQ2CDBC
p2m_reactivate "P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral.P2MQ2CDBC"

end P11_CDBC_INT
p2m_reactivate "P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral.P2MQ2CDBC"

open P2MQ2CDBC in

theorem solution.{u', v', w'}
    (O : Type u') [CommRing O] (O' : Type v') [CommRing O'] [Algebra O O']
    (A : Type w') [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O O' A) ∧
    CartierDual.dualBaseChangeLin O O' A 1 = 1 ∧
    (∀ x y : O' ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O O' A (x * y)
          = CartierDual.dualBaseChangeLin O O' A x * CartierDual.dualBaseChangeLin O O' A y) ∧
    (∀ w : O' ⊗[O] CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O O' A) (CartierDual.dualBaseChangeLin O O' A)
            (Coalgebra.comul (R := O') w)
          = Coalgebra.comul (R := O') (CartierDual.dualBaseChangeLin O O' A w)) ∧
    (∀ (g : CartierDual O A) (x : O' ⊗[O] A),
        CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := O') x)) := by
  refine ⟨bcLin_bijective, bcLin_one, bcLin_mul, fun w => ?_, bc_one_tmul_antipode⟩
  exact map_bc_comul w

end S_CartierDual_dualBaseChangeLin_bijective_integral
end P2MW
export P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral (solution)
