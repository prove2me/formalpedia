-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.indexInMoveToFront_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:07.270609+00:00
-- url     : https://prove2.me/submissions/4d810927-56a4-4ebc-a3e2-ff5114db2f7e

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
theorem _root_.solution (j : ℕ) : indexInMoveToFront j j = 0 := by
  simp [indexInMoveToFront]
end FunctorialResolution.EmbeddedResolution
