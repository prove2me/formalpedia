-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.orderFamily_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:25:09.95906+00:00
-- url     : https://prove2.me/submissions/b3b88e6b-9ea6-4089-903e-7b6b7923649a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PrincipalizationRules
namespace FunctorialResolution.EmbeddedResolution.PrincipalizationRules
theorem _root_.solution (B : PrincipalizationRules.{u}) (D : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    B.orderFamily D T = B.orderRed T (fun S _ j => D j S) := rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
