-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.indexBeforeMoveToFront_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:49:05.549333+00:00
-- url     : https://prove2.me/submissions/bec42e48-43d4-4943-a324-4c8293d943f3

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
theorem _root_.solution (j : ℕ) : indexBeforeMoveToFront j 0 = j := rfl
end FunctorialResolution.EmbeddedResolution
