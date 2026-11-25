-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.maxOrderFamily_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:22:48.223804+00:00
-- url     : https://prove2.me/submissions/1c4d9f4b-7097-4a25-b8ea-dfbb1bb9e11d

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
theorem _root_.solution (B : PrincipalizationRules.{u}) (A : PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) :
    B.maxOrderFamily A T = B.maxOrderRed T (fun S _ => A S) := rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
