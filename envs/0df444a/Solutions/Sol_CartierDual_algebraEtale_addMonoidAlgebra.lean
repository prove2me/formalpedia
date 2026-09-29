-- Prove2me | solution 1 for CartierDual.algebraEtale_addMonoidAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/4f8abf44-4461-549d-84e5-e637aa418004

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_algebraEtale_addMonoidAlgebra

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace MultEtale

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]

noncomputable def ev : CartierDual R (AddMonoidAlgebra R M) →ₐ[R] (M → R) where
  toFun φ x := φ (AddMonoidAlgebra.single x 1)
  map_one' := by
    ext x
    simp [CartierDual.one_apply]
  map_mul' φ ψ := by
    ext x
    simp only [Pi.mul_apply]
    rw [CartierDual.mul_apply, AddMonoidAlgebra.comul_single]
    simp [TensorProduct.dualDistrib_apply]
  map_zero' := by ext; rfl
  map_add' _ _ := by ext; rfl
  commutes' r := by
    ext x
    simp [CartierDual.algebraMap_apply]

theorem ev_apply (φ : CartierDual R (AddMonoidAlgebra R M)) (x : M) :
    ev R M φ x = φ (AddMonoidAlgebra.single x 1) := rfl

theorem ev_bijective : Function.Bijective (ev R M) := by
  constructor
  · intro φ ψ h
    have key : CartierDual.toDual R _ φ = CartierDual.toDual R _ ψ := by
      apply AddMonoidAlgebra.lhom_ext'
      intro x
      apply LinearMap.ext_ring
      have hx := congrFun h x
      simp only [ev_apply] at hx
      rw [LinearMap.comp_apply, LinearMap.comp_apply, AddMonoidAlgebra.lsingle_apply]
      exact hx
    exact (CartierDual.toDual R _).injective key
  · intro f
    refine ⟨CartierDual.ofDual R _
      ((Finsupp.linearCombination R f).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap), ?_⟩
    ext x
    rw [ev_apply, CartierDual.ofDual_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      AddMonoidAlgebra.coeffLinearEquiv_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.linearCombination_single, one_smul]

end MultEtale

theorem solution (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Finite M] :
    Algebra.Etale R (CartierDual R (AddMonoidAlgebra R M)) :=
  Algebra.Etale.of_equiv (AlgEquiv.ofBijective (MultEtale.ev R M) (MultEtale.ev_bijective R M)).symm

#print axioms solution

end S_CartierDual_algebraEtale_addMonoidAlgebra
end P2MW
export P2MW.S_CartierDual_algebraEtale_addMonoidAlgebra (solution)
