-- Prove2me | solution 1 for CartierDual.exists_bialgEquiv_monoidAlgebra_of_points
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/2eb8a3a6-78dc-5b33-864a-6df9f06ecb55

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points

set_option autoImplicit false

open scoped TensorProduct

namespace CartierDual
p2m_export "CartierDual" "toDual ofDual ext mul_apply one_def one_apply comul_pairing tmul_eq_of_pairing_eq counit_apply"
namespace PointsEvalAux
p2m_open "CartierDual"

section Functionals

variable (R : Type*) [CommRing R] (Γ : Type*) [CommMonoid Γ]

noncomputable def ofFun (f : Γ → R) : CartierDual R (MonoidAlgebra R Γ) :=
  CartierDual.ofDual R _ ((Finsupp.lsum R fun x => LinearMap.id.smulRight (f x) : (Γ →₀ R) →ₗ[R] R) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

theorem ofFun_single (f : Γ → R) (x : Γ) (r : R) :
    ofFun R Γ f (MonoidAlgebra.single x r) = r * f x := by
  show ((Finsupp.lsum R fun x => LinearMap.id.smulRight (f x) : (Γ →₀ R) →ₗ[R] R) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) (MonoidAlgebra.single x r) = r * f x
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, Finsupp.lsum_single]
  simp [smul_eq_mul]

variable {R Γ} in

theorem eq_of_forall_single {φ ψ : CartierDual R (MonoidAlgebra R Γ)}
    (h : ∀ x : Γ, φ (MonoidAlgebra.single x 1) = ψ (MonoidAlgebra.single x 1)) : φ = ψ := by
  apply CartierDual.ext
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g => exact h g
  | add a b ha hb =>
    show φ (a + b) = ψ (a + b)
    rw [map_add, map_add, ha, hb]
  | smul r a ha =>
    show φ (r • a) = ψ (r • a)
    rw [map_smul, map_smul, ha]

theorem ofFun_apply_single_one (f : Γ → R) (x : Γ) : ofFun R Γ f (MonoidAlgebra.single x 1) = f x := by
  rw [ofFun_single, one_mul]

omit [CommMonoid Γ] in
theorem comul_single_one (x : Γ) :
    Coalgebra.comul (R := R) (MonoidAlgebra.single x (1 : R)) =
      MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single x 1 := by
  rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  rfl

theorem mul_apply_single_one (φ ψ : CartierDual R (MonoidAlgebra R Γ)) (x : Γ) :
    (φ * ψ) (MonoidAlgebra.single x 1) = φ (MonoidAlgebra.single x 1) * ψ (MonoidAlgebra.single x 1) := by
  rw [CartierDual.mul_apply, comul_single_one, TensorProduct.dualDistrib_apply]
  rfl

theorem one_apply_single_one (x : Γ) : (1 : CartierDual R (MonoidAlgebra R Γ)) (MonoidAlgebra.single x 1) = 1 := by
  rw [CartierDual.one_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]

end Functionals

section Points

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]

theorem convMul_apply_repr (f g : WithConv (A →ₐ[R] R)) (a : A) {ι𝓡 : Type*} (𝓡 : Coalgebra.Repr R a ι𝓡) :
    (WithConv.ofConv (f * g)) a =
      ∑ i ∈ 𝓡.index, (WithConv.ofConv f) (𝓡.left i) * (WithConv.ofConv g) (𝓡.right i) := by
  have h := Coalgebra.Repr.convMul_apply 𝓡 (WithConv.toConv (WithConv.ofConv f).toLinearMap)
    (WithConv.toConv (WithConv.ofConv g).toLinearMap)
  rw [LinearMap.convMul_apply] at h
  exact h

private theorem _root_.CartierDual.PointsEvalAux.convOne_apply (a : A) :
    (WithConv.ofConv (1 : WithConv (A →ₐ[R] R))) a = algebraMap R R (Coalgebra.counit a) := by
  first
  | rfl
  | exact AlgHom.convOne_apply (R := R) a

p2m_export "CartierDual.PointsEvalAux" "convOne_apply"

theorem convMul_apply_eq_mul'_map (f g : WithConv (A →ₐ[R] R)) (a : A) :
    (WithConv.ofConv (f * g)) a =
      LinearMap.mul' R R (TensorProduct.map (WithConv.ofConv f).toLinearMap (WithConv.ofConv g).toLinearMap
        (Coalgebra.comul a)) := by
  classical
  let 𝓡 := Coalgebra.Repr.arbitrary R a
  rw [convMul_apply_repr f g a 𝓡]
  conv_rhs => rw [← 𝓡.eq]
  simp only [map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply, AlgHom.toLinearMap_apply]

end Points

section Main

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
variable (Γ : Type*) [CommMonoid Γ]
variable (y : Γ →* WithConv (A →ₐ[R] R))

noncomputable def evalPts : A →ₗ[R] CartierDual R (MonoidAlgebra R Γ) where
  toFun a := ofFun R Γ (fun x => y x a)
  map_add' a b := by
    apply eq_of_forall_single; intro x
    show ofFun R Γ _ _ = ofFun R Γ _ (MonoidAlgebra.single x 1) + ofFun R Γ _ (MonoidAlgebra.single x 1)
    simp only [ofFun_apply_single_one]
    exact map_add (WithConv.ofConv (y x)) a b
  map_smul' r a := by
    apply eq_of_forall_single; intro x
    show ofFun R Γ _ _ = r • ofFun R Γ _ (MonoidAlgebra.single x 1)
    simp only [ofFun_apply_single_one]
    exact map_smul (WithConv.ofConv (y x)) r a

theorem evalPts_apply_single (a : A) (x : Γ) : evalPts R A Γ y a (MonoidAlgebra.single x 1) = y x a :=
  ofFun_apply_single_one R Γ _ x

theorem evalPts_mul (a b : A) : evalPts R A Γ y (a * b) = evalPts R A Γ y a * evalPts R A Γ y b := by
  apply eq_of_forall_single; intro x
  rw [mul_apply_single_one, evalPts_apply_single, evalPts_apply_single, evalPts_apply_single]
  exact map_mul (WithConv.ofConv (y x)) a b

theorem evalPts_one : evalPts R A Γ y 1 = 1 := by
  apply eq_of_forall_single; intro x
  rw [evalPts_apply_single, one_apply_single_one]
  exact map_one (WithConv.ofConv (y x))

noncomputable def evalPtsAlgHom : A →ₐ[R] CartierDual R (MonoidAlgebra R Γ) :=
  AlgHom.ofLinearMap (evalPts R A Γ y) (evalPts_one R A Γ y) (evalPts_mul R A Γ y)

theorem evalPtsAlgHom_apply (a : A) : evalPtsAlgHom R A Γ y a = evalPts R A Γ y a := rfl

theorem evalPts_bijective (hy : Function.Bijective fun (a : A) (x : Γ) => y x a) :
    Function.Bijective (evalPts R A Γ y) := by
  have hE : ∀ a, (fun x : Γ => evalPts R A Γ y a (MonoidAlgebra.single x 1)) = fun x => y x a := by
    intro a; funext x; exact evalPts_apply_single R A Γ y a x
  constructor
  · intro a b hab
    apply hy.1
    show (fun x => y x a) = fun x => y x b
    rw [← hE a, ← hE b, hab]
  · intro φ
    obtain ⟨a, ha⟩ := hy.2 (fun x => φ (MonoidAlgebra.single x 1))
    refine ⟨a, eq_of_forall_single fun x => ?_⟩
    rw [evalPts_apply_single]
    exact congrFun ha x

variable [Finite Γ]

theorem counit_evalPts (a : A) : Coalgebra.counit (R := R) (evalPts R A Γ y a) = Coalgebra.counit (R := R) a := by
  rw [CartierDual.counit_apply, MonoidAlgebra.one_def, evalPts_apply_single, map_one]
  exact convOne_apply (R := R) (A := A) a

theorem comul_evalPts_pairing (a : A) (x z : Γ) :
    TensorProduct.dualDistrib R (MonoidAlgebra R Γ) (MonoidAlgebra R Γ)
        (TensorProduct.map (CartierDual.toDual R _).toLinearMap (CartierDual.toDual R _).toLinearMap
          (Coalgebra.comul (R := R) (evalPts R A Γ y a)))
        (MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single z 1) =
    TensorProduct.dualDistrib R (MonoidAlgebra R Γ) (MonoidAlgebra R Γ)
        (TensorProduct.map (CartierDual.toDual R _).toLinearMap (CartierDual.toDual R _).toLinearMap
          (TensorProduct.map (evalPts R A Γ y) (evalPts R A Γ y) (Coalgebra.comul (R := R) a)))
        (MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single z 1) := by
  rw [CartierDual.comul_pairing, MonoidAlgebra.single_mul_single, mul_one, evalPts_apply_single, map_mul]
  rw [convMul_apply_eq_mul'_map]
  generalize Coalgebra.comul (R := R) a = t
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul u v =>
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.dualDistrib_apply]
    change (WithConv.ofConv (y x)) u * (WithConv.ofConv (y z)) v =
      (evalPts R A Γ y u) (MonoidAlgebra.single x 1) * (evalPts R A Γ y v) (MonoidAlgebra.single z 1)
    rw [evalPts_apply_single, evalPts_apply_single]
  | add t₁ t₂ h₁ h₂ => simp only [map_add, LinearMap.add_apply, h₁, h₂]

theorem comul_evalPts (a : A) :
    Coalgebra.comul (R := R) (evalPts R A Γ y a) =
      TensorProduct.map (evalPts R A Γ y) (evalPts R A Γ y) (Coalgebra.comul (R := R) a) := by
  apply CartierDual.tmul_eq_of_pairing_eq
  intro b c
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    induction c using MonoidAlgebra.induction_on with
    | of z => exact comul_evalPts_pairing R A Γ y a x z
    | add c₁ c₂ h₁ h₂ =>
      simp only [TensorProduct.tmul_add, map_add] at *
      rw [h₁, h₂]
    | smul r c hc =>
      simp only [TensorProduct.tmul_smul, map_smul] at *
      rw [hc]
  | add b₁ b₂ h₁ h₂ =>
    simp only [TensorProduct.add_tmul, map_add] at *
    rw [h₁, h₂]
  | smul r b hb =>
    rw [← TensorProduct.smul_tmul', map_smul, map_smul, hb]

noncomputable def evalPtsBialgHom : A →ₐc[R] CartierDual R (MonoidAlgebra R Γ) :=
  { evalPtsAlgHom R A Γ y with
    counit_comp := by
      ext a
      exact counit_evalPts R A Γ y a
    map_comp_comul := by
      ext a
      exact (comul_evalPts R A Γ y a).symm
    map_smul' := fun r a => map_smul (evalPts R A Γ y) r a }

theorem evalPtsBialgHom_apply (a : A) : evalPtsBialgHom R A Γ y a = evalPts R A Γ y a := rfl

end Main

end CartierDual.PointsEvalAux

open CartierDual.PointsEvalAux in
theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    (Γ : Type*) [CommMonoid Γ] [Finite Γ]
    (y : Γ →* WithConv (A →ₐ[R] R))
    (hy : Function.Bijective fun (a : A) (x : Γ) => y x a) :
    ∃ ψ : A ≃ₐc[R] CartierDual R (MonoidAlgebra R Γ),
      ∀ (a : A) (x : Γ), ψ a (MonoidAlgebra.single x 1) = y x a :=
  ⟨BialgEquiv.ofBijective (evalPtsBialgHom R A Γ y) (evalPts_bijective R A Γ y hy),
    fun a x => evalPts_apply_single R A Γ y a x⟩

end S_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points
end P2MW
export P2MW.S_CartierDual_exists_bialgEquiv_monoidAlgebra_of_points (solution)
