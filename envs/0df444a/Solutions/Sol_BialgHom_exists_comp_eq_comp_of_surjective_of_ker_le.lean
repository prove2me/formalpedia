-- Prove2me | solution 1 for BialgHom.exists_comp_eq_comp_of_surjective_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0ed49d93-7d6e-5d75-b25e-4ea318a013b2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u v

theorem solution
    {R : Type u} [CommRing R]
    {H₁ H₂ H₁' H₂' : Type v} [CommRing H₁] [Bialgebra R H₁] [CommRing H₂] [Bialgebra R H₂]
    [CommRing H₁'] [Bialgebra R H₁'] [CommRing H₂'] [Bialgebra R H₂']
    (π₁ : H₁ →ₐc[R] H₁') (π₂ : H₂ →ₐc[R] H₂') (hπ₂ : Function.Surjective π₂)
    (r : H₂ →ₐc[R] H₁) (hker : ∀ x : H₂, π₂ x = 0 → π₁ (r x) = 0) :
    ∃ r' : H₂' →ₐc[R] H₁', r'.comp π₂ = π₁.comp r ∧
      (Function.Surjective π₁ → Function.Surjective r → Function.Surjective r') := by
  classical

  have hker' : RingHom.ker (π₂ : H₂ →+* H₂') ≤ RingHom.ker ((π₁ : H₁ →+* H₁').comp (r : H₂ →+* H₁)) := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    exact hker x hx
  let f : H₂' →+* H₁' := RingHom.liftOfSurjective (π₂ : H₂ →+* H₂') hπ₂ ⟨(π₁ : H₁ →+* H₁').comp (r : H₂ →+* H₁), hker'⟩
  have hf : ∀ x : H₂, f (π₂ x) = π₁ (r x) := by
    intro x
    exact RingHom.liftOfRightInverse_comp_apply (π₂ : H₂ →+* H₂') _ _ _ x

  let fa : H₂' →ₐ[R] H₁' :=
    { f with
      commutes' := fun c => by
        have h := hf (algebraMap R H₂ c)
        rw [AlgHomClass.commutes π₂, AlgHomClass.commutes r, AlgHomClass.commutes π₁] at h
        exact h }
  have hfa : ∀ x : H₂, fa (π₂ x) = π₁ (r x) := hf

  have hcounit : (Bialgebra.counitAlgHom R H₁').comp fa = Bialgebra.counitAlgHom R H₂' := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    change Coalgebra.counit (fa (π₂ x)) = Coalgebra.counit (π₂ x)
    rw [hfa, CoalgHomClass.counit_comp_apply, CoalgHomClass.counit_comp_apply,
      CoalgHomClass.counit_comp_apply]

  have hcomul : (Algebra.TensorProduct.map fa fa).comp (Bialgebra.comulAlgHom R H₂') =
      (Bialgebra.comulAlgHom R H₁').comp fa := by
    apply AlgHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    change Algebra.TensorProduct.map fa fa (Coalgebra.comul (π₂ x)) = Coalgebra.comul (fa (π₂ x))
    rw [hfa, ← CoalgHomClass.map_comp_comul_apply, ← CoalgHomClass.map_comp_comul_apply,
      ← CoalgHomClass.map_comp_comul_apply]

    have key : (Algebra.TensorProduct.map fa fa).toLinearMap ∘ₗ
        TensorProduct.map (π₂ : H₂ →ₗ[R] H₂') (π₂ : H₂ →ₗ[R] H₂') =
        TensorProduct.map (π₁ : H₁ →ₗ[R] H₁') (π₁ : H₁ →ₗ[R] H₁') ∘ₗ
          TensorProduct.map (r : H₂ →ₗ[R] H₁) (r : H₂ →ₗ[R] H₁) := by
      apply TensorProduct.ext'
      intro a b
      simp [hfa]
    exact congrArg (fun g => g (Coalgebra.comul (R := R) x)) key
  refine ⟨BialgHom.ofAlgHom fa hcounit hcomul, ?_, ?_⟩
  · apply BialgHom.coe_algHom_injective
    apply AlgHom.ext
    intro x
    exact hfa x
  · intro hπ₁ hr z
    obtain ⟨y, rfl⟩ := hπ₁ z
    obtain ⟨x, rfl⟩ := hr y
    exact ⟨π₂ x, hfa x⟩

end S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le
end P2MW
export P2MW.S_BialgHom_exists_comp_eq_comp_of_surjective_of_ker_le (solution)
