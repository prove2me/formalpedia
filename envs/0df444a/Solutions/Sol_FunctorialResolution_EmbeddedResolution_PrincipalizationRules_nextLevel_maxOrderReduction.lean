-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.nextLevel_maxOrderReduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:32:22.961407+00:00
-- url     : https://prove2.me/submissions/a4d6f00b-3896-4ad6-94fe-b598dad6e8fc

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
theorem _root_.solution (B : PrincipalizationRules.{u}) (L : OrderReductionData.{u}) :
    (B.nextLevel L).maxOrderRed =
      B.maxOrderFamily (B.orderFamily (fun j => B.divisorFamily L.maxOrderRed j)) := rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
