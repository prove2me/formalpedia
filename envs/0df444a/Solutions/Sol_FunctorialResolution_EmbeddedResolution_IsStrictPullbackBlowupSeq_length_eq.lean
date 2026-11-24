-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.IsStrictPullbackBlowupSeq.length_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:47:36.564997+00:00
-- url     : https://prove2.me/submissions/79a43c94-223e-4d8f-b63f-96b836919c66

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations

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
namespace IsStrictPullbackBlowupSeq
theorem _root_.solution {X' X : Scheme.{u}} {φ : X' ⟶ X}
    {B' : SequenceOfBlowups X'} {B : SequenceOfBlowups X} (h : IsStrictPullbackBlowupSeq φ B' B) :
    B'.length = B.length := h.1
end IsStrictPullbackBlowupSeq
end FunctorialResolution.EmbeddedResolution
