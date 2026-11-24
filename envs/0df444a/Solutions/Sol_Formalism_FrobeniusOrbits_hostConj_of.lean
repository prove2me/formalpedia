-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostConj_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:17:30.505861+00:00
-- url     : https://prove2.me/submissions/d81e352a-63ff-4ef2-b631-bdc4091077d7

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_JumpSets
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ConjReal
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_conj_main
import Theorems.Thm_Formalism_FrobeniusOrbits_ConjReal_aE_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_ne_zero_of_sq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_UnitConjugation_phi_conj
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_ne_zero_of_sq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open ConjReal
namespace Formalism.FrobeniusOrbits
theorem _root_.solution (hGal : HostGalois) (hSpec : HostGalSpec) : HostConj := by
  intro e q d hqd L _ _ ζ a b h
  obtain ⟨hG, _, _, hbij⟩ := hGal e q d hqd L ζ a b h
  have := hG
  obtain ⟨_, σc, _, _, hσc, hconj⟩ := conj_main hGal hSpec hqd h
  have hq : 0 < q := hqd.1.pos
  have haE := aE_sq h
  have hTC : IsTotallyComplex (hostE ζ a b) := by
    refine ⟨fun w => ?_⟩
    rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]
    intro hw
    have h2 := RingHom.congr_fun hw (aE ζ a b)
    rw [ComplexEmbedding.conjugate_coe_eq, UnitConjugation.phi_conj hq haE] at h2
    have h3 : (2 : ℂ) * w.embedding (aE ζ a b) = 0 := by linear_combination -h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact two_ne_zero h4
    · exact (map_ne_zero _).2 (UnitConjugation.ne_zero_of_sq hq haE) h4
  have hCM : IsCMField (hostE ζ a b) := by
    refine IsCMField.of_forall_isConj (hostE ζ a b) (σ := σc) (fun φ => ?_)
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact (hconj φ x).symm
  refine ⟨hCM, fun φ σ => ⟨fun hx => ?_, fun hσ => ?_⟩⟩
  · have hσ : σ = σc := AlgEquiv.ext fun x => φ.injective (by rw [hx, hconj])
    rw [hσ, hσc]
  · have hσ' : σ = σc := hbij.1 (hσ.trans hσc.symm)
    subst hσ'
    exact hconj φ
end Formalism.FrobeniusOrbits
