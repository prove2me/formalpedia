-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.indexInMoveToFront_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:06.525648+00:00
-- url     : https://prove2.me/submissions/4616776a-07cb-4e28-8e75-201e54fb5d58

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront

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
variable {α : Type*}
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (j : ℕ) : Function.Injective (indexInMoveToFront j) := by
  intro a b hab
  simp only [indexInMoveToFront] at hab
  split_ifs at hab <;> omega
end FunctorialResolution.EmbeddedResolution
