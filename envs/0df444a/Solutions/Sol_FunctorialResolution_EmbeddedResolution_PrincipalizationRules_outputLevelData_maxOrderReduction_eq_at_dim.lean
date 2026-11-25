-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.outputLevelData_maxOrderReduction_eq_at_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:21:22.199504+00:00
-- url     : https://prove2.me/submissions/4ea8b6f3-e42e-4ad9-b446-cb1e65887618

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_PrincipalizationRules_outputLevelData_maxOrderReduction_eq_of_le

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
theorem _root_.solution (B : PrincipalizationRules.{u}) (T : MarkedIdealWithBoundary.{u}) {N : ℕ}
    (hT : T.krullDimSucc ≤ N) :
    (B.outputLevelData N).maxOrderRed T = (B.outputLevelData T.krullDimSucc).maxOrderRed T :=
  outputLevelData_maxOrderReduction_eq_of_le B hT T le_rfl
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
