-- Prove2me | solution 1 for CartierDual.exists_algEquiv_monoidAlgebra_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/c2c01a9a-6923-53e5-9393-38929e1be601

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi

set_option autoImplicit false

open scoped TensorProduct

namespace P2mS17E

variable (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ]

noncomputable def evalLin : CartierDual R (MonoidAlgebra R Γ) →ₗ[R] (Γ → R) where
  toFun φ x := φ (MonoidAlgebra.single x 1)
  map_add' φ ψ := by ext x; rfl
  map_smul' r φ := by ext x; rfl

noncomputable def ofFun (f : Γ → R) : CartierDual R (MonoidAlgebra R Γ) :=
  CartierDual.ofDual R _ ((Finsupp.lsum R fun x => LinearMap.id.smulRight (f x) : (Γ →₀ R) →ₗ[R] R) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap)

theorem ofFun_single (f : Γ → R) (x : Γ) (r : R) : ofFun R Γ f (MonoidAlgebra.single x r) = r * f x := by
  show ((Finsupp.lsum R fun x => LinearMap.id.smulRight (f x) : (Γ →₀ R) →ₗ[R] R) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) (MonoidAlgebra.single x r) = r * f x
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
    MonoidAlgebra.coeff_single, Finsupp.lsum_single]
  simp [smul_eq_mul]

noncomputable def evalEquiv : CartierDual R (MonoidAlgebra R Γ) ≃ₗ[R] (Γ → R) where
  toLinearMap := evalLin R Γ
  invFun := ofFun R Γ
  left_inv φ := by
    apply CartierDual.ext
    intro a
    show (CartierDual.toDual R _ (ofFun R Γ (fun x => φ (MonoidAlgebra.single x 1)))) a = φ a

    induction a using MonoidAlgebra.induction_on with
    | of g =>
      show ofFun R Γ _ (MonoidAlgebra.single g 1) = φ (MonoidAlgebra.of R Γ g)
      rw [ofFun_single, one_mul]; rfl
    | add a b ha hb =>
      show ofFun R Γ _ (a + b) = φ (a + b)
      rw [map_add, map_add]; exact congrArg₂ (· + ·) ha hb
    | smul r a ha =>
      show ofFun R Γ _ (r • a) = φ (r • a)
      rw [map_smul, map_smul]; exact congrArg (r • ·) ha
  right_inv f := by
    ext x
    show ofFun R Γ f (MonoidAlgebra.single x 1) = f x
    rw [ofFun_single, one_mul]

theorem evalEquiv_apply (φ : CartierDual R (MonoidAlgebra R Γ)) (x : Γ) :
    evalEquiv R Γ φ x = φ (MonoidAlgebra.single x 1) := rfl

theorem comul_single_one (x : Γ) :
    Coalgebra.comul (R := R) (MonoidAlgebra.single x (1 : R)) =
      MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single x 1 := by
  rw [MonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul]
  rfl

theorem evalEquiv_mul (φ ψ : CartierDual R (MonoidAlgebra R Γ)) :
    evalEquiv R Γ (φ * ψ) = evalEquiv R Γ φ * evalEquiv R Γ ψ := by
  ext x
  rw [Pi.mul_apply, evalEquiv_apply, evalEquiv_apply, evalEquiv_apply, CartierDual.mul_apply,
    comul_single_one, TensorProduct.dualDistrib_apply]
  rfl

theorem evalEquiv_one : evalEquiv R Γ 1 = 1 := by
  ext x
  rw [evalEquiv_apply, CartierDual.one_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply, Pi.one_apply]

noncomputable def evalAlgEquiv : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R) :=
  AlgEquiv.ofLinearEquiv (evalEquiv R Γ) (evalEquiv_one R Γ) (evalEquiv_mul R Γ)

end P2mS17E

open P2mS17E in
theorem solution
    (R : Type*) [CommRing R] (Γ : Type*) [CommGroup Γ] [Fintype Γ] :
    ∃ e : CartierDual R (MonoidAlgebra R Γ) ≃ₐ[R] (Γ → R),
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x : Γ), e φ x = φ (MonoidAlgebra.single x 1)) ∧
      (∀ (φ : CartierDual R (MonoidAlgebra R Γ)) (x y : Γ),
        TensorProduct.dualDistrib R (MonoidAlgebra R Γ) (MonoidAlgebra R Γ)
          (TensorProduct.map (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap
            (CartierDual.toDual R (MonoidAlgebra R Γ)).toLinearMap (Coalgebra.comul (R := R) φ))
          (MonoidAlgebra.single x 1 ⊗ₜ[R] MonoidAlgebra.single y 1) = φ (MonoidAlgebra.single (x * y) 1)) ∧
      (∀ φ : CartierDual R (MonoidAlgebra R Γ), Coalgebra.counit (R := R) φ = φ 1) := by
  refine ⟨evalAlgEquiv R Γ, fun φ x => rfl, fun φ x y => ?_, fun φ => CartierDual.counit_apply φ⟩
  rw [CartierDual.comul_pairing, MonoidAlgebra.single_mul_single, mul_one]

end S_CartierDual_exists_algEquiv_monoidAlgebra_pi
end P2MW
export P2MW.S_CartierDual_exists_algEquiv_monoidAlgebra_pi (solution)
