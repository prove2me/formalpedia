-- Prove2me | solution 1 for Formalism.HC.HostRaw.hostEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:39:34.943587+00:00
-- url     : https://prove2.me/submissions/b755c795-c396-468e-bca9-e0b60c1d3518

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.HostRaw
theorem _root_.solution (ψ : H.E →+* ℂ) :
    Function.Bijective (fun σ : H.E ≃ₐ[ℚ] H.E => ψ.comp (σ : H.E →+* H.E)) := by
  haveI := H.galois
  have hinj : Function.Injective (fun σ : H.E ≃ₐ[ℚ] H.E => ψ.comp (σ : H.E →+* H.E)) := by
    intro σ τ h
    ext x
    exact ψ.injective (congrArg (fun g : H.E →+* ℂ => g x) h)
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by rw [Fintype.card_eq_nat_card, IsGalois.card_aut_eq_finrank, NumberField.Embeddings.card]⟩
end Formalism.HC.HostRaw
