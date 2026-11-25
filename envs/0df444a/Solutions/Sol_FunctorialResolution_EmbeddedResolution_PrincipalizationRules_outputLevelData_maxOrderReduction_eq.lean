-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_maxOrderReduction_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:16.118386+00:00
-- url     : https://prove2.me/submissions/97715a89-f003-44ee-9fd2-8a927810f5cf

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
theorem _root_.solution (B : PrincipalizationRules.{u}) (n : ℕ) :
    (B.outputLevelData n).maxOrderRed = B.maxOrderFamily (B.outputLevelData n).orderRed := rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
