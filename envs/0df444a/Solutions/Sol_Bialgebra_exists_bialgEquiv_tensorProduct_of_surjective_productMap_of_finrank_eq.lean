-- Prove2me | solution 1 for Bialgebra.exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ea833b8b-e9e0-5a6e-821f-d010b0b11281

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq

set_option autoImplicit false

open scoped TensorProduct

namespace SplitAlgAux

variable {k : Type*} [Field k] {A C : Type*} [CommRing A] [CommRing C] [Bialgebra k A] [Bialgebra k C]

noncomputable def prodBialgHom (ρ₀ ρ₁ : A →ₐc[k] C) : A ⊗[k] A →ₐc[k] C :=
  (Bialgebra.mulBialgHom k C).comp (Bialgebra.TensorProduct.map ρ₀ ρ₁)

theorem prodBialgHom_apply (ρ₀ ρ₁ : A →ₐc[k] C) (x : A ⊗[k] A) :
    prodBialgHom ρ₀ ρ₁ x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a b =>
    rw [Algebra.TensorProduct.productMap_apply_tmul]
    show Bialgebra.mulBialgHom k C (Bialgebra.TensorProduct.map ρ₀ ρ₁ (a ⊗ₜ[k] b)) = _
    rw [Bialgebra.TensorProduct.map_tmul]
    exact Algebra.TensorProduct.lmul'_apply_tmul (R := k) (ρ₀ a) (ρ₁ b)
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end SplitAlgAux

open SplitAlgAux

theorem solution
    (k : Type*) [Field k] (A C : Type*) [CommRing A] [CommRing C] [Bialgebra k A] [Bialgebra k C]
    [FiniteDimensional k A] [FiniteDimensional k C]
    (ρ₀ ρ₁ : A →ₐc[k] C)
    (hsurj : Function.Surjective (Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C)))
    (hrank : Module.finrank k C = Module.finrank k A * Module.finrank k A) :
    ∃ κ : C ≃ₐc[k] A ⊗[k] A,
      (∀ a : A, κ.symm (a ⊗ₜ[k] 1) = ρ₀ a) ∧ (∀ a : A, κ.symm (1 ⊗ₜ[k] a) = ρ₁ a) ∧
      ∀ x : A ⊗[k] A, κ.symm x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x := by
  classical
  let π : A ⊗[k] A →ₐc[k] C := prodBialgHom ρ₀ ρ₁
  have hπ : ∀ x, π x = Algebra.TensorProduct.productMap (ρ₀ : A →ₐ[k] C) (ρ₁ : A →ₐ[k] C) x :=
    prodBialgHom_apply ρ₀ ρ₁
  have hπsurj : Function.Surjective π := by
    intro c; obtain ⟨x, rfl⟩ := hsurj c; exact ⟨x, hπ x⟩
  have hdim : Module.finrank k (A ⊗[k] A) = Module.finrank k C := by
    rw [Module.finrank_tensorProduct, hrank]
  have hπinj : Function.Injective π :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := π.toLinearMap)).2 hπsurj
  refine ⟨(BialgEquiv.ofBijective π ⟨hπinj, hπsurj⟩).symm, fun a => ?_, fun a => ?_, fun x => ?_⟩
  · show π (a ⊗ₜ[k] 1) = ρ₀ a
    rw [hπ, Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]; rfl
  · show π (1 ⊗ₜ[k] a) = ρ₁ a
    rw [hπ, Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]; rfl
  · show π x = _
    exact hπ x

end S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq
end P2MW
export P2MW.S_Bialgebra_exists_bialgEquiv_tensorProduct_of_surjective_productMap_of_finrank_eq (solution)
