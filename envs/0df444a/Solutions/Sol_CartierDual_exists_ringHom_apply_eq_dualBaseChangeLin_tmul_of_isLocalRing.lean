-- Prove2me | solution 1 for CartierDual.exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b01ae6e7-1643-574c-b2e8-a2299b8afe6b

import Mathlib
import Theorems.Thm_CartierDual_dualBaseChangeLin_bijective_integral
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing

set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {B : Type v} [CommRing B] [HopfAlgebra R B] [Module.Finite R B] [Module.Free R B] :
    ∃ r : CartierDual R B →+* CartierDual (ResidueField R) (ResidueField R ⊗[R] B),
      (∀ φ, r φ = CartierDual.dualBaseChangeLin R (ResidueField R) B ((1 : ResidueField R) ⊗ₜ[R] φ)) ∧
      Function.Surjective r ∧
      RingHom.ker r = (maximalIdeal R).map (algebraMap R (CartierDual R B)) := by
  classical
  set κ := ResidueField R with hκ
  obtain ⟨hbij, hone, hmul, -, -⟩ := CartierDual.dualBaseChangeLin_bijective_integral R κ B

  let D : κ ⊗[R] CartierDual R B →+* CartierDual κ (κ ⊗[R] B) :=
    { toFun := CartierDual.dualBaseChangeLin R κ B
      map_one' := hone
      map_mul' := hmul
      map_zero' := map_zero _
      map_add' := fun x y => map_add _ x y }

  let I : CartierDual R B →+* κ ⊗[R] CartierDual R B :=
    (Algebra.TensorProduct.includeRight : CartierDual R B →ₐ[R] κ ⊗[R] CartierDual R B).toRingHom
  have hI : ∀ φ, I φ = (1 : κ) ⊗ₜ[R] φ := fun _ => rfl
  refine ⟨D.comp I, fun φ => rfl, ?_, ?_⟩
  ·
    exact hbij.2.comp (Algebra.TensorProduct.includeRight_surjective (CartierDual R B)
      (IsLocalRing.residue_surjective : Function.Surjective (algebraMap R κ)))
  ·
    have hker : ∀ φ : CartierDual R B,
        φ ∈ RingHom.ker (D.comp I) ↔ φ ∈ maximalIdeal R • (⊤ : Submodule R (CartierDual R B)) := by
      intro φ
      rw [RingHom.mem_ker, RingHom.comp_apply, hI]
      constructor
      · intro h0
        have h1 : (1 : κ) ⊗ₜ[R] φ = 0 := hbij.1 (by rw [map_zero]; exact h0)
        have h1' : ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] φ : (R ⧸ maximalIdeal R) ⊗[R] CartierDual R B) = 0 := h1
        have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul (CartierDual R B) (maximalIdeal R)) h1'
        rw [map_zero, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h2
        exact h2
      · intro hφ
        have h2 : (TensorProduct.quotTensorEquivQuotSMul (CartierDual R B) (maximalIdeal R))
            ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] φ) = 0 := by
          rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
          exact hφ
        have h1' : ((1 : R ⧸ maximalIdeal R) ⊗ₜ[R] φ : (R ⧸ maximalIdeal R) ⊗[R] CartierDual R B) = 0 := by
          rw [← map_zero (TensorProduct.quotTensorEquivQuotSMul (CartierDual R B) (maximalIdeal R))] at h2
          exact (TensorProduct.quotTensorEquivQuotSMul (CartierDual R B) (maximalIdeal R)).injective h2
        have h1 : (1 : κ) ⊗ₜ[R] φ = 0 := h1'
        show D ((1 : κ) ⊗ₜ[R] φ) = 0
        rw [h1, map_zero]

    apply le_antisymm
    · intro φ hφ
      have hφ' := (hker φ).mp hφ
      refine Submodule.smul_induction_on hφ' ?_ ?_
      · intro r hr x _
        rw [Algebra.smul_def, Algebra.commutes]
        exact Ideal.mul_mem_left _ x (Ideal.mem_map_of_mem _ hr)
      · intro x y hx hy
        exact Ideal.add_mem _ hx hy
    · intro φ hφ
      apply (hker φ).mpr
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hφ
      · rintro _ ⟨r, hr, rfl⟩
        rw [Algebra.algebraMap_eq_smul_one]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · exact Submodule.zero_mem _
      · intro x y _ _ hx hy
        exact Submodule.add_mem _ hx hy
      · intro s x _ hx

        refine Submodule.smul_induction_on hx ?_ ?_
        · intro r hr y _
          show s * (r • y) ∈ _
          rw [Algebra.mul_smul_comm]
          exact Submodule.smul_mem_smul hr Submodule.mem_top
        · intro y z hy hz
          show s * (y + z) ∈ _
          rw [mul_add]
          exact Submodule.add_mem _ hy hz

end S_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing
end P2MW
export P2MW.S_CartierDual_exists_ringHom_apply_eq_dualBaseChangeLin_tmul_of_isLocalRing (solution)
