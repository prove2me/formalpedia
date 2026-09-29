-- Prove2me | solution 1 for CartierDual.exists_algHomEquiv_groupLike
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fc058039-9ad5-5cea-bff3-d0b5f06286cc

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_algHomEquiv_groupLike

set_option autoImplicit false
set_option maxHeartbeats 3200000

open scoped TensorProduct

universe u v w

namespace P2mS17G

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H]
variable (B : Type w) [CommRing B] [Algebra R B]

noncomputable section

def pairB (φ : CartierDual R H) : B ⊗[R] H →ₗ[B] B :=
  Module.Dual.baseChange B (CartierDual.toDual R H φ)

variable {R H B}

@[scoped simp] theorem pairB_tmul (φ : CartierDual R H) (s : B) (h : H) : pairB R H B φ (s ⊗ₜ[R] h) = φ h • s := rfl

theorem pairB_eq_rid_lTensor (φ : CartierDual R H) (x : B ⊗[R] H) :
    pairB R H B φ x = TensorProduct.rid R B (LinearMap.lTensor B (CartierDual.toDual R H φ) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pairB_add (φ χ : CartierDual R H) (x : B ⊗[R] H) :
    pairB R H B (φ + χ) x = pairB R H B φ x + pairB R H B χ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, add_zero]
  | tmul s h =>
    rw [pairB_tmul, pairB_tmul, pairB_tmul]
    show (φ h + χ h) • s = φ h • s + χ h • s
    rw [add_smul]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel

theorem pairB_smul (r : R) (φ : CartierDual R H) (x : B ⊗[R] H) :
    pairB R H B (r • φ) x = r • pairB R H B φ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul s h =>
    rw [pairB_tmul, pairB_tmul]
    show (r • φ h) • s = r • φ h • s
    rw [smul_assoc]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

variable (R H B)

def psiOf (x : B ⊗[R] H) : CartierDual R H →ₗ[R] B where
  toFun φ := pairB R H B φ x
  map_add' φ χ := pairB_add φ χ x
  map_smul' r φ := pairB_smul r φ x

@[scoped simp] theorem psiOf_apply (x : B ⊗[R] H) (φ : CartierDual R H) : psiOf R H B x φ = pairB R H B φ x := rfl

abbrev ι : Type v := Module.Free.ChooseBasisIndex R H
def bH : Module.Basis (ι R H) R H := Module.Free.chooseBasis R H

scoped instance : Fintype (ι R H) := Module.Free.ChooseBasisIndex.fintype R H

def δ (i : ι R H) : CartierDual R H := CartierDual.ofDual R H ((bH R H).coord i)

@[scoped simp] theorem δ_apply (i : ι R H) (h : H) : δ R H i h = (bH R H).repr h i := rfl

@[scoped simp] theorem toDual_δ (i : ι R H) : CartierDual.toDual R H (δ R H i) = (bH R H).coord i := rfl

def elemOf (L : CartierDual R H →ₗ[R] B) : B ⊗[R] H := ∑ i, L (δ R H i) ⊗ₜ[R] bH R H i

theorem pairB_elemOf (L : CartierDual R H →ₗ[R] B) (φ : CartierDual R H) :
    pairB R H B φ (elemOf R H B L) = L φ := by
  simp only [elemOf, map_sum, pairB_tmul]
  have key : ∑ i, φ (bH R H i) • δ R H i = φ := by
    apply (CartierDual.toDual R H).injective
    rw [map_sum]
    simp only [map_smul, toDual_δ]
    exact (bH R H).sum_dual_apply_smul_coord (CartierDual.toDual R H φ)
  calc ∑ i, φ (bH R H i) • L (δ R H i) = L (∑ i, φ (bH R H i) • δ R H i) := by
        rw [map_sum]; simp only [map_smul]
    _ = L φ := by rw [key]

theorem basis_repr_eq_pairB (x : B ⊗[R] H) (i : ι R H) :
    (Algebra.TensorProduct.basis B (bH R H)).repr x i = pairB R H B (δ R H i) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul s h =>
    rw [Algebra.TensorProduct.basis_repr_tmul, pairB_tmul, δ_apply, Finsupp.smul_apply,
      Finsupp.mapRange_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy]

theorem ext_of_pairB {x y : B ⊗[R] H} (h : ∀ φ : CartierDual R H, pairB R H B φ x = pairB R H B φ y) : x = y :=
  (Algebra.TensorProduct.basis B (bH R H)).ext_elem fun i => by rw [basis_repr_eq_pairB, basis_repr_eq_pairB, h]

theorem elemOf_psiOf (x : B ⊗[R] H) : elemOf R H B (psiOf R H B x) = x :=
  ext_of_pairB R H B fun φ => by rw [pairB_elemOf, psiOf_apply]

end

end P2mS17G
p2m_reactivate "P2MW.S_CartierDual_exists_algHomEquiv_groupLike.P2mS17G"

namespace P2mS17G

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H]
variable (B : Type w) [CommRing B] [Algebra R B]

noncomputable section

def pair₂ (φ χ : CartierDual R H) : (B ⊗[R] H) ⊗[B] (B ⊗[R] H) →ₗ[B] B :=
  TensorProduct.dualDistrib B (B ⊗[R] H) (B ⊗[R] H) (pairB R H B φ ⊗ₜ[B] pairB R H B χ)

variable {R H B}

@[scoped simp] theorem pair₂_tmul (φ χ : CartierDual R H) (u v : B ⊗[R] H) :
    pair₂ R H B φ χ (u ⊗ₜ[B] v) = pairB R H B φ u * pairB R H B χ v := rfl

theorem counit_eq_pairB_one (x : B ⊗[R] H) : Coalgebra.counit (R := B) x = pairB R H B 1 x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pair₂_comul (φ χ : CartierDual R H) (x : B ⊗[R] H) :
    pair₂ R H B φ χ (Coalgebra.comul (R := B) x) = pairB R H B (φ * χ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h =>
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, pairB_tmul, CartierDual.mul_apply]

    generalize Coalgebra.comul (R := R) h = w
    induction w using TensorProduct.induction_on with
    | zero => rw [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero, LinearMap.map_zero, zero_smul]
    | tmul h₁ h₂ =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, pair₂_tmul, pairB_tmul, pairB_tmul,
        TensorProduct.dualDistrib_apply, CartierDual.toDual_apply, CartierDual.toDual_apply,
        smul_mul_smul_comm, one_mul]
    | add w₁ w₂ h₁ h₂ => rw [TensorProduct.tmul_add, map_add, map_add, h₁, h₂, map_add, add_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem basis₂_repr_eq_pair₂ (z : (B ⊗[R] H) ⊗[B] (B ⊗[R] H)) (i j : ι R H) :
    ((Algebra.TensorProduct.basis B (bH R H)).tensorProduct (Algebra.TensorProduct.basis B (bH R H))).repr z (i, j) =
      pair₂ R H B (δ R H i) (δ R H j) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul u v =>
    rw [Module.Basis.tensorProduct_repr_tmul_apply, pair₂_tmul, basis_repr_eq_pairB, basis_repr_eq_pairB,
      smul_eq_mul, mul_comm]
  | add x y hx hy => rw [map_add, map_add, Finsupp.add_apply, hx, hy]

theorem ext_of_pair₂ {z₁ z₂ : (B ⊗[R] H) ⊗[B] (B ⊗[R] H)}
    (h : ∀ φ χ : CartierDual R H, pair₂ R H B φ χ z₁ = pair₂ R H B φ χ z₂) : z₁ = z₂ :=
  ((Algebra.TensorProduct.basis B (bH R H)).tensorProduct (Algebra.TensorProduct.basis B (bH R H))).ext_elem
    fun ⟨i, j⟩ => by rw [basis₂_repr_eq_pair₂, basis₂_repr_eq_pair₂, h]

variable (R H B)

def toGroupLike (ψ : CartierDual R H →ₐ[R] B) : GroupLike B (B ⊗[R] H) where
  val := elemOf R H B ψ.toLinearMap
  isGroupLikeElem_val :=
    { counit_eq_one := by
        rw [counit_eq_pairB_one, pairB_elemOf]
        exact map_one ψ
      comul_eq_tmul_self := by
        apply ext_of_pair₂; intro φ χ
        rw [pair₂_comul, pair₂_tmul, pairB_elemOf, pairB_elemOf, pairB_elemOf]
        exact map_mul ψ φ χ }

@[scoped simp] theorem toGroupLike_val (ψ : CartierDual R H →ₐ[R] B) :
    (toGroupLike R H B ψ).val = elemOf R H B ψ.toLinearMap := rfl

def ofGroupLike (g : GroupLike B (B ⊗[R] H)) : CartierDual R H →ₐ[R] B :=
  AlgHom.ofLinearMap (psiOf R H B g.val)
    (by
      show pairB R H B 1 g.val = 1
      rw [← counit_eq_pairB_one]
      exact g.isGroupLikeElem_val.counit_eq_one)
    (fun φ χ => by
      show pairB R H B (φ * χ) g.val = pairB R H B φ g.val * pairB R H B χ g.val
      rw [← pair₂_comul, g.isGroupLikeElem_val.comul_eq_tmul_self, pair₂_tmul])

@[scoped simp] theorem ofGroupLike_apply (g : GroupLike B (B ⊗[R] H)) (φ : CartierDual R H) :
    ofGroupLike R H B g φ = pairB R H B φ g.val := rfl

def algHomEquivGroupLike : (CartierDual R H →ₐ[R] B) ≃ GroupLike B (B ⊗[R] H) where
  toFun := toGroupLike R H B
  invFun := ofGroupLike R H B
  left_inv ψ := by
    apply AlgHom.ext; intro φ
    rw [ofGroupLike_apply, toGroupLike_val, pairB_elemOf]
    rfl
  right_inv g := GroupLike.val_injective (by
    rw [toGroupLike_val]
    exact elemOf_psiOf R H B g.val)

theorem algHomEquivGroupLike_val (ψ : CartierDual R H →ₐ[R] B) :
    (algHomEquivGroupLike R H B ψ).val = elemOf R H B ψ.toLinearMap := rfl

theorem pin (ψ : CartierDual R H →ₐ[R] B) (φ : CartierDual R H) :
    TensorProduct.rid R B (LinearMap.lTensor B (CartierDual.toDual R H φ) (algHomEquivGroupLike R H B ψ).val) = ψ φ := by
  rw [← pairB_eq_rid_lTensor, algHomEquivGroupLike_val, pairB_elemOf]
  rfl

end
p2m_reactivate "P2MW.S_CartierDual_exists_algHomEquiv_groupLike.P2mS17G"

end P2mS17G
p2m_reactivate "P2MW.S_CartierDual_exists_algHomEquiv_groupLike.P2mS17G"

namespace P2mS17G

variable (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H]
variable (B : Type w) [CommRing B] [Algebra R B]

noncomputable section

variable {R H B}

theorem elemOf_eq_one (ψ₀ : CartierDual R H →ₐ[R] B) (h0 : ∀ φ, ψ₀ φ = algebraMap R B (φ 1)) :
    elemOf R H B ψ₀.toLinearMap = 1 := by
  apply ext_of_pairB; intro φ
  rw [pairB_elemOf, Algebra.TensorProduct.one_def, pairB_tmul, ← Algebra.algebraMap_eq_smul_one]
  exact h0 φ

theorem psiOf_add (x y : B ⊗[R] H) : psiOf R H B (x + y) = psiOf R H B x + psiOf R H B y := by
  apply LinearMap.ext; intro φ; simp only [psiOf_apply, map_add, LinearMap.add_apply]

theorem psiOf_zero : psiOf R H B 0 = 0 := by
  apply LinearMap.ext; intro φ; simp only [psiOf_apply, map_zero, LinearMap.zero_apply]

theorem mul'_map_psiOf_tmul_tmul (s s' : B) (h h' : H) (w : CartierDual R H ⊗[R] CartierDual R H) :
    LinearMap.mul' R B (TensorProduct.map (psiOf R H B (s ⊗ₜ[R] h)) (psiOf R H B (s' ⊗ₜ[R] h')) w) =
      (TensorProduct.dualDistrib R H H
        (TensorProduct.map (CartierDual.toDual R H).toLinearMap (CartierDual.toDual R H).toLinearMap w) (h ⊗ₜ[R] h')) •
        (s * s') := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, zero_smul]
  | tmul φ χ =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, psiOf_apply, psiOf_apply, pairB_tmul, pairB_tmul,
      TensorProduct.map_tmul, TensorProduct.dualDistrib_apply, smul_mul_smul_comm]
    rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, add_smul]

theorem pairB_mul (φ : CartierDual R H) (x₁ x₂ : B ⊗[R] H) :
    pairB R H B φ (x₁ * x₂) =
      LinearMap.mul' R B (TensorProduct.map (psiOf R H B x₁) (psiOf R H B x₂) (Coalgebra.comul (R := R) φ)) := by
  induction x₁ using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, psiOf_zero, TensorProduct.map_zero_left, LinearMap.zero_apply, map_zero]
  | tmul s h =>
    induction x₂ using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, psiOf_zero, TensorProduct.map_zero_right, LinearMap.zero_apply, map_zero]
    | tmul s' h' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairB_tmul, mul'_map_psiOf_tmul_tmul]
      erw [CartierDual.comul_pairing (R := R) (A := H) φ h h']
    | add x y hx hy =>
      rw [mul_add, map_add, hx, hy, psiOf_add, TensorProduct.map_add_right, LinearMap.add_apply, map_add]
  | add x y hx hy =>
    rw [add_mul, map_add, hx, hy, psiOf_add, TensorProduct.map_add_left, LinearMap.add_apply, map_add]

theorem elemOf_convMul (ψ₁ ψ₂ ψ₃ : CartierDual R H →ₐ[R] B)
    (hconv : WithConv.toConv ψ₃.toLinearMap = WithConv.toConv ψ₁.toLinearMap * WithConv.toConv ψ₂.toLinearMap) :
    elemOf R H B ψ₃.toLinearMap = elemOf R H B ψ₁.toLinearMap * elemOf R H B ψ₂.toLinearMap := by
  apply ext_of_pairB; intro φ
  have h3 : ψ₃.toLinearMap φ =
      LinearMap.mul' R B (TensorProduct.map ψ₁.toLinearMap ψ₂.toLinearMap (Coalgebra.comul (R := R) φ)) := by
    have := congrArg (fun F : WithConv (CartierDual R H →ₗ[R] B) => F.ofConv φ) hconv
    simpa [LinearMap.convMul_def] using this
  have e1 : psiOf R H B (elemOf R H B ψ₁.toLinearMap) = ψ₁.toLinearMap :=
    LinearMap.ext fun χ => by rw [psiOf_apply, pairB_elemOf]
  have e2 : psiOf R H B (elemOf R H B ψ₂.toLinearMap) = ψ₂.toLinearMap :=
    LinearMap.ext fun χ => by rw [psiOf_apply, pairB_elemOf]
  rw [pairB_elemOf, pairB_mul, e1, e2]
  exact h3

theorem pairB_map {B' : Type w} [CommRing B'] [Algebra R B'] (τ : B →ₐ[R] B') (φ : CartierDual R H) (x : B ⊗[R] H) :
    pairB R H B' φ (Algebra.TensorProduct.map τ (AlgHom.id R H) x) = τ (pairB R H B φ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s h =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, pairB_tmul, pairB_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem elemOf_comp {B' : Type w} [CommRing B'] [Algebra R B'] (τ : B →ₐ[R] B') (ψ : CartierDual R H →ₐ[R] B) :
    elemOf R H B' (τ.comp ψ).toLinearMap = Algebra.TensorProduct.map τ (AlgHom.id R H) (elemOf R H B ψ.toLinearMap) := by
  apply ext_of_pairB; intro φ
  rw [pairB_elemOf, pairB_map, pairB_elemOf]
  rfl

end
p2m_reactivate "P2MW.S_CartierDual_exists_algHomEquiv_groupLike.P2mS17G"

end P2mS17G
p2m_reactivate "P2MW.S_CartierDual_exists_algHomEquiv_groupLike.P2mS17G"

open P2mS17G in
theorem solution
    (R : Type u) [CommRing R] (H : Type v) [CommRing H] [Bialgebra R H] [Module.Finite R H] [Module.Free R H] :
    ∃ e : (∀ (B : Type w) [CommRing B] [Algebra R B], (CartierDual R H →ₐ[R] B) ≃ GroupLike B (TensorProduct R B H)),
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ : CartierDual R H →ₐ[R] B) (φ : CartierDual R H),
          TensorProduct.rid R B (LinearMap.lTensor B (CartierDual.toDual R H φ) (e B ψ).val) = ψ φ) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₀ : CartierDual R H →ₐ[R] B),
          (∀ φ, ψ₀ φ = algebraMap R B (φ 1)) → (e B ψ₀).val = 1) ∧
      (∀ (B : Type w) [CommRing B] [Algebra R B] (ψ₁ ψ₂ ψ₃ : CartierDual R H →ₐ[R] B),
          WithConv.toConv ψ₃.toLinearMap = WithConv.toConv ψ₁.toLinearMap * WithConv.toConv ψ₂.toLinearMap →
          (e B ψ₃).val = (e B ψ₁).val * (e B ψ₂).val) ∧
      (∀ (B B' : Type w) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B'] (τ : B →ₐ[R] B')
          (ψ : CartierDual R H →ₐ[R] B),
          (e B' (τ.comp ψ)).val = Algebra.TensorProduct.map τ (AlgHom.id R H) (e B ψ).val) :=
  ⟨fun B _ _ => algHomEquivGroupLike R H B,
    fun B _ _ ψ φ => pin R H B ψ φ,
    fun B _ _ ψ₀ h0 => elemOf_eq_one ψ₀ h0,
    fun B _ _ ψ₁ ψ₂ ψ₃ hconv => elemOf_convMul ψ₁ ψ₂ ψ₃ hconv,
    fun B B' _ _ _ _ τ ψ => elemOf_comp τ ψ⟩

end S_CartierDual_exists_algHomEquiv_groupLike
end P2MW
export P2MW.S_CartierDual_exists_algHomEquiv_groupLike (solution)
