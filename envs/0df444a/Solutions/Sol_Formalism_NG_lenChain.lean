-- Prove2me | solution 1 for Formalism.NG.lenChain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:21.001802+00:00
-- url     : https://prove2.me/submissions/f39a3139-2cef-431c-b0dc-9a40ded92c74

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatLenChain := by
  intro O H Zc C _ _ _ _ _ _ _ Ψ cl S hS
  let φ : LinearMap.range Ψ →ₗ[O] C := cl ∘ₗ (LinearMap.range Ψ).subtype
  have h1 := IdempotentNormalFormsRhoFacts.length_eq_ker_add_range Ψ
  have h2 := IdempotentNormalFormsRhoFacts.length_eq_ker_add_range φ
  have hk : Module.length O (LinearMap.ker φ) ≤
      Module.length O ↥(LinearMap.range Ψ ⊓ LinearMap.ker cl) := by
    refine Module.length_le_of_injective
      (((LinearMap.range Ψ).subtype ∘ₗ (LinearMap.ker φ).subtype).codRestrict _
        fun x => Submodule.mem_inf.mpr ⟨x.1.2, LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp x.2)⟩)
      ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have hr : Module.length O (LinearMap.range φ) ≤ Module.length O S := by
    refine le_trans ?_ (IdempotentNormalFormsRhoFacts.length_mono (A := LinearMap.range φ) ?_)
    · exact le_rfl
    · rintro _ ⟨⟨z, hz⟩, rfl⟩
      obtain ⟨h, rfl⟩ := LinearMap.mem_range.mp hz
      exact hS ⟨h, rfl⟩
  rw [h1, h2, add_assoc]
  gcongr
end Formalism.NG
