-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.mem_coe_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:17:25.65221+00:00
-- url     : https://prove2.me/submissions/30d6f677-29f6-4875-ac6e-68da1a705119

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) (I : Ideal (𝓞 E)) (z : E) :
    z ∈ (I : FractionalIdeal (𝓞 E)⁰ E) ↔
      σ z ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_coeIdeal, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨σ • w, Ideal.smul_mem_pointwise_smul σ w I hw, rfl⟩
  · rintro ⟨w, hw, he⟩
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hw
    refine ⟨σ⁻¹ • w, hw, ?_⟩
    show σ⁻¹ (w : E) = z
    have he' : (w : E) = σ z := he
    rw [he']
    exact σ.symm_apply_apply z
end Formalism.HermitianLattices.StabilizerLevels.PfB
