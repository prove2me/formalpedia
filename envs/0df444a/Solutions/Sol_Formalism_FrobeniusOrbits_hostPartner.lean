-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostPartner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:38.999623+00:00
-- url     : https://prove2.me/submissions/670ee89b-008a-41cf-b87f-71541c879893

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CardExtendedGaloisGroup
import Theorems.Thm_Formalism_FrobeniusOrbits_Misc2_units_ne_one_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Misc2
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostPartner := by
  intro e τ hτ
  rw [mem_Psi_iff] at hτ
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [Set.mem_ofPred_eq, mem_Psi_iff, units_ne_one_iff] at hg
    show _ ∈ Psi e
    rw [mem_Psi_iff]
    simp [cc, c0, hg, hτ]
  · intro g _ g' _ hgg
    simpa using hgg
  · intro t ht
    rw [SetLike.mem_coe, mem_Psi_iff] at ht
    refine ⟨(cc e)⁻¹ * t * τ⁻¹, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, mem_Psi_iff]
      simp [cc, c0, ht, hτ]
    · simp only
      group
end Formalism.FrobeniusOrbits
