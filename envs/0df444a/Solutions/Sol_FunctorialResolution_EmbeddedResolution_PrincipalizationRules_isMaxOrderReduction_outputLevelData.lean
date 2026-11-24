-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isMaxOrderReduction_outputLevelData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:10.340656+00:00
-- url     : https://prove2.me/submissions/12b629e7-5eea-481c-bd72-2aff0332ecef

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_isOrderReduction_outputLevelData

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
theorem _root_.solution (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed (B.outputLevelData n).orderRed :=
  hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed
    (isOrderReduction_outputLevelData B hB n)
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
