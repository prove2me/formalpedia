-- Prove2me | solution 1 for FullLevelTate.exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/6626f509-51ab-5224-a98a-4efd9dbea6d4

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    (lam : ℕ) [Fact lam.Prime] (O' : Type) [CommRing O'] [Algebra ℤ_[lam] O']
    (K : Type) [CommRing K] [Algebra O' K] [Algebra ℚ_[lam] K]
    (hOK : ∀ z : ℤ_[lam], algebraMap O' K (algebraMap ℤ_[lam] O' z) = algebraMap ℚ_[lam] K (z : ℚ_[lam]))
    (T : Type) [AddCommMonoid T] [Module ℤ_[lam] T] :
    ∃ e : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T),
      ∀ (c : K) (a : O') (x : T),
        e (c ⊗ₜ[O'] (a ⊗ₜ[ℤ_[lam]] x)) = (algebraMap O' K a * c) ⊗ₜ[ℚ_[lam]] ((1 : ℚ_[lam]) ⊗ₜ[ℤ_[lam]] x) := by
  classical
  letI : Algebra ℤ_[lam] K := ((algebraMap O' K).comp (algebraMap ℤ_[lam] O')).toAlgebra
  haveI hT1 : IsScalarTower ℤ_[lam] O' K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hT2 : IsScalarTower ℤ_[lam] ℚ_[lam] K := by
    refine IsScalarTower.of_algebraMap_eq (fun z => ?_)
    show algebraMap O' K (algebraMap ℤ_[lam] O' z) = _
    rw [hOK z]
    rfl
  let e₁ : K ⊗[O'] (O' ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℤ_[lam]] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[lam] O' K K T
  let e₂ : K ⊗[ℚ_[lam]] (ℚ_[lam] ⊗[ℤ_[lam]] T) ≃ₗ[K] K ⊗[ℤ_[lam]] T :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ_[lam] ℚ_[lam] K K T
  refine ⟨e₁.trans e₂.symm, fun c a x => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  simp only [e₁, e₂, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, Algebra.smul_def, map_one,
    one_mul]

end S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq
end P2MW
export P2MW.S_FullLevelTate_exists_linearEquiv_cancelBaseChange_of_algebraMap_eq (solution)
