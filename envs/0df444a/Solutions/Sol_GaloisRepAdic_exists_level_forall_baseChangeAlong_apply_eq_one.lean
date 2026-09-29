-- Prove2me | solution 1 for GaloisRepAdic.exists_level_forall_baseChangeAlong_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e58eb24d-505d-5530-9fbf-78c19ff2ce51

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one

set_option autoImplicit false

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (K : ℕ) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ {B : Type} [CommRing B] [IsLocalRing B] (f : A →+* B) (hf : IsLocalHom f),
        (∀ a ∈ IsLocalRing.maximalIdeal A ^ K, f a = 0) →
        ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, s x = x) →
          (ρ.baseChangeAlong f hf).ρ s = 1 := by
  obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous K
  refine ⟨L, hL, fun {B} _ _ f hf hK s hs => ?_⟩
  letI : Algebra A B := f.toAlgebra
  have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A ^ K) • (⊤ : Submodule A ρ.V), ∀ b : B,
      TensorProduct.tmul A b x = (0 : TensorProduct A B ρ.V) := by
    intro x hx b
    refine Submodule.smul_induction_on
      (p := fun x => TensorProduct.tmul A b x = (0 : TensorProduct A B ρ.V)) hx ?_ ?_
    · intro a ha w _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        RingHom.algebraMap_toAlgebra, hK a ha, zero_mul, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  refine LinearMap.ext fun w => ?_
  show (ρ.ρ s).baseChange B w = w
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero]
  | tmul b v =>
    rw [LinearMap.baseChange_tmul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
    exact hkill _ (h1 s hs v) b
  | add x y hx hy => rw [map_add, hx, hy]

end S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one
end P2MW
export P2MW.S_GaloisRepAdic_exists_level_forall_baseChangeAlong_apply_eq_one (solution)
