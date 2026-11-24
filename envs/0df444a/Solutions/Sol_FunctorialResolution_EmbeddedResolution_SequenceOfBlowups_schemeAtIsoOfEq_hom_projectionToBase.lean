-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:40.728212+00:00
-- url     : https://prove2.me/submissions/076e3d1b-3a71-4857-b07f-3a3878c60c94

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable {X : Scheme.{u}}
namespace FunctorialResolution.EmbeddedResolution
namespace SequenceOfBlowups
theorem _root_.solution (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst h
  simp [SequenceOfBlowups.schemeAtIsoOfEq]
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution
