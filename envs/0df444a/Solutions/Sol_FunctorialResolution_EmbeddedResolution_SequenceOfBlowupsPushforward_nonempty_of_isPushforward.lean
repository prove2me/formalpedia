-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward.nonempty_of_isPushforward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:43.351646+00:00
-- url     : https://prove2.me/submissions/763a7f69-232f-45dd-8764-3276abc40585

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_StrictTransformClosedImmersion
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_ClosedEmbedding_PushforwardUniqueness

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
namespace FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
theorem _root_.solution {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X} (h : IsPushforwardBlowupSeq j BS B) :
    Nonempty (SequenceOfBlowupsPushforward j BS B) := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  refine ⟨⟨hlen, fun i hi => σ i (by omega), fun i hi => hci i _, ?_, ?_, ?_⟩⟩
  · exact h0
  · intro i hi
    exact hstep i (by omega)
  · intro i hi
    exact hcent i (by omega)
end FunctorialResolution.EmbeddedResolution.SequenceOfBlowupsPushforward
