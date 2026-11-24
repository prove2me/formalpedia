-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.length_quotient_twist_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:27.335725+00:00
-- url     : https://prove2.me/submissions/ff7dddc9-6376-4c0c-bc2f-e88a1c76cef6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar
import Theorems.Thm_Formalism_HermitianLattices_LocalLatticeBases_length_quotient_power_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : LengthQuotientTwistFormula := by
  intro R _ M _ _ T hT N c
  obtain ⟨V, hV⟩ : ∃ V : Module.End R N, V = T • LinearMap.id := ⟨_, rfl⟩
  have hVinj : Function.Injective V := by
    rw [injective_iff_map_eq_zero]; intro x hx
    apply Subtype.ext; apply hT; have := congrArg Subtype.val hx; simpa [hV] using this
  have hVc : ∀ x : N, ((V^c) x : M) = T^c • (x:M) := by
    intro x
    induction c with
    | zero => simp
    | succ c ih =>
      have hz : ∀ z : N, ((V z : N) : M) = T • (z:M) := by intro z; rw [hV]; simp
      rw [pow_succ', Module.End.mul_apply, hz, ih, pow_succ', mul_smul]
  have it := length_quotient_power_injective R N V hVinj c
  rw [← hV, ← it]
  have h1 : LinearMap.range (V^c) ≤ (N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M))).comap N.subtype := by
    rintro _ ⟨y, rfl⟩; exact ⟨y, y.2, by simp [hVc]⟩
  have h2 : N.map ((T ^ c) • (LinearMap.id : M →ₗ[R] M)) ≤ N.comap LinearMap.id := by
    rintro _ ⟨y, hy, rfl⟩; exact N.smul_mem _ hy
  have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ N.subtype h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
  · rw [key, add_comm]
  · rw [injective_iff_map_eq_zero]
    intro a
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      intro hx
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
      rw [hVc]; simpa using hyx
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
  · intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
      constructor
      · intro hx
        exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, by rw [Submodule.mapQ_apply]; rfl⟩
      · rintro ⟨a, ha⟩
        induction a using Submodule.Quotient.induction_on with
        | H y =>
          rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
          have := h2 ha
          simp only [Submodule.mem_comap, LinearMap.id_coe, id_eq, Submodule.subtype_apply] at this ⊢
          have h3 := N.sub_mem y.2 this
          simpa using h3
end Formalism.HermitianLattices.LocalLatticeBases
