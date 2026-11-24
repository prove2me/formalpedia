-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.isomorphic_refl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:47:39.710187+00:00
-- url     : https://prove2.me/submissions/46952643-5ba6-4c01-b148-c616ec500fc8

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
namespace SequenceOfBlowups
theorem _root_.solution {X : Scheme.{u}} (B : SequenceOfBlowups X) : B.Isomorphic B := by
  refine ⟨rfl, fun i _ => Iso.refl _, ?_, ?_, ?_⟩ <;> simp
end SequenceOfBlowups
end FunctorialResolution.EmbeddedResolution
