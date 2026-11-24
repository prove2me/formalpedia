-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.mem_div_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:37:36.594267+00:00
-- url     : https://prove2.me/submissions/f50d729d-9f8c-41ce-a489-a9bdf87f25e6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_HermitianLattices_StabilizerLevels_PfB_mem_coe_smul

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
theorem _root_.solution (σ : E ≃ₐ[ℚ] E) (I J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (hJ' : σ • J ≠ ⊥) (y : E) :
    y ∈ (I : FractionalIdeal (𝓞 E)⁰ E) * (J : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔
      σ y ∈ ((σ • I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        ((σ • J : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv,
    FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ),
    FractionalIdeal.mem_div_iff_of_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hJ')]
  constructor
  · intro h β' hβ'
    have e : σ (σ.symm β') = β' := σ.apply_symm_apply β'
    rw [← e] at hβ' ⊢
    rw [← mem_coe_smul] at hβ'
    rw [← map_mul, ← mem_coe_smul]
    exact h _ hβ'
  · intro h β hβ
    rw [mem_coe_smul σ, map_mul]
    exact h _ ((mem_coe_smul σ J β).1 hβ)
end Formalism.HermitianLattices.StabilizerLevels.PfB
