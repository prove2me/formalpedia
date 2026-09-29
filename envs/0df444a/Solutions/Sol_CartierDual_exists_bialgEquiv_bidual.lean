-- Prove2me | solution 1 for CartierDual.exists_bialgEquiv_bidual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/166767ef-402a-5f43-aa7e-86b76a9ce6d4

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_bialgEquiv_bidual

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

open scoped TensorProduct

namespace P2mS17B

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
variable [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A]

noncomputable def ev : A →ₗ[R] CartierDual R (CartierDual R A) where
  toFun a := CartierDual.ofDual R (CartierDual R A)
    { toFun := fun φ => φ a
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := by
    apply CartierDual.ext; intro φ
    show φ (a + b) = φ a + φ b
    exact map_add φ a b
  map_smul' r a := by
    apply CartierDual.ext; intro φ
    show φ (r • a) = r • φ a
    exact map_smul φ r a

theorem ev_apply (a : A) (φ : CartierDual R A) : ev R A a φ = φ a := rfl

theorem ev_bijective : Function.Bijective (ev R A) :=
  (Module.evalEquiv R A).bijective

theorem flip₁ (a b : A) (w : CartierDual R A ⊗[R] CartierDual R A) :
    TensorProduct.dualDistrib R (CartierDual R A) (CartierDual R A)
        (CartierDual.toDual R _ (ev R A a) ⊗ₜ[R] CartierDual.toDual R _ (ev R A b)) w =
      TensorProduct.dualDistrib R A A
        (TensorProduct.map (CartierDual.toDual R A).toLinearMap (CartierDual.toDual R A).toLinearMap w) (a ⊗ₜ[R] b) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul φ ψ =>
    rw [TensorProduct.dualDistrib_apply, TensorProduct.map_tmul, TensorProduct.dualDistrib_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, LinearMap.add_apply, hx, hy]

theorem flip₂ (φ ψ : CartierDual R A) (z : A ⊗[R] A) :
    TensorProduct.dualDistrib R (CartierDual R A) (CartierDual R A)
        (TensorProduct.map (CartierDual.toDual R (CartierDual R A)).toLinearMap
          (CartierDual.toDual R (CartierDual R A)).toLinearMap (TensorProduct.map (ev R A) (ev R A) z)) (φ ⊗ₜ[R] ψ) =
      TensorProduct.dualDistrib R A A (CartierDual.toDual R A φ ⊗ₜ[R] CartierDual.toDual R A ψ) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | tmul a b => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem ev_mul (a b : A) : ev R A (a * b) = ev R A a * ev R A b := by
  apply CartierDual.ext; intro φ
  rw [CartierDual.mul_apply, flip₁, CartierDual.comul_pairing]
  rfl

theorem ev_one : ev R A 1 = 1 := by
  apply CartierDual.ext; intro φ
  rw [CartierDual.one_apply, CartierDual.counit_apply]
  rfl

noncomputable def evAlgEquiv : A ≃ₐ[R] CartierDual R (CartierDual R A) :=
  AlgEquiv.ofBijective (AlgHom.ofLinearMap (ev R A) (ev_one R A) (ev_mul R A)) (ev_bijective R A)

theorem evAlgEquiv_apply (a : A) : evAlgEquiv R A a = ev R A a := rfl

theorem counit_comp :
    (Bialgebra.counitAlgHom R (CartierDual R (CartierDual R A))).comp (evAlgEquiv R A : A →ₐ[R] _) =
      Bialgebra.counitAlgHom R A := by
  apply AlgHom.ext; intro a
  rw [AlgHom.comp_apply, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply, AlgEquiv.coe_algHom,
    evAlgEquiv_apply]
  exact (CartierDual.counit_apply (R := R) (A := CartierDual R A) (ev R A a)).trans (CartierDual.one_apply a)

theorem map_comp_comul :
    (Algebra.TensorProduct.map (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))
        (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))).comp (Bialgebra.comulAlgHom R A) =
      (Bialgebra.comulAlgHom R (CartierDual R (CartierDual R A))).comp (evAlgEquiv R A : A →ₐ[R] _) := by
  apply AlgHom.ext; intro a
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, Bialgebra.comulAlgHom_apply,
    AlgEquiv.coe_algHom, evAlgEquiv_apply]
  have hmap : ∀ w : A ⊗[R] A,
      (Algebra.TensorProduct.map (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))
        (evAlgEquiv R A : A →ₐ[R] CartierDual R (CartierDual R A))) w =
      TensorProduct.map (ev R A) (ev R A) w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a b => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [hmap]
  apply CartierDual.tmul_eq_of_pairing_eq
  intro φ ψ
  rw [flip₂ R A φ ψ]
  erw [CartierDual.comul_pairing (R := R) (A := CartierDual R A) (ev R A a) φ ψ]
  rw [ev_apply, CartierDual.mul_apply]

end P2mS17B

open P2mS17B in
theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Free R A] [Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a :=
  ⟨BialgEquiv.ofAlgEquiv (evAlgEquiv R A) (counit_comp R A) (map_comp_comul R A), fun _ _ => rfl⟩

end S_CartierDual_exists_bialgEquiv_bidual
end P2MW
export P2MW.S_CartierDual_exists_bialgEquiv_bidual (solution)
