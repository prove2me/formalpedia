-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsPushforwardBlowupSeq.isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:26:58.5363+00:00
-- url     : https://prove2.me/submissions/56de7baa-791e-43ad-975b-1017486ec142

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
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_nonempty_of_isPushforward
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_SequenceOfBlowupsPushforward_isomorphic

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
namespace FunctorialResolution.EmbeddedResolution
namespace IsPushforwardBlowupSeq
theorem _root_.solution {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (h' : IsPushforwardBlowupSeq j BS B') :
    B.Isomorphic B' := by
  obtain ⟨d⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h
  obtain ⟨d'⟩ := SequenceOfBlowupsPushforward.nonempty_of_isPushforward j h'
  exact d.isomorphic d'
end IsPushforwardBlowupSeq
end FunctorialResolution.EmbeddedResolution
