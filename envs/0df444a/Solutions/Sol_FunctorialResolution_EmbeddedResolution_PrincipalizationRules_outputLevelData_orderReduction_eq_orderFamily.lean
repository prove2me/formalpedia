-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_orderReduction_eq_orderFamily
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:26.926335+00:00
-- url     : https://prove2.me/submissions/67da3b83-804d-4c9a-87e3-059db398a17b

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
    (B.outputLevelData n).orderRed = B.orderFamily (fun j => B.levelDivisorFamily n j) := rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
