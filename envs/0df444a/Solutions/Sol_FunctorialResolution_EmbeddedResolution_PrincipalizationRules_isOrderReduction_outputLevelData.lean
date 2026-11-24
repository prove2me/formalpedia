-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.PrincipalizationRules.isOrderReduction_outputLevelData
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:38:31.355899+00:00
-- url     : https://prove2.me/submissions/9372313f-fc5e-4761-97b2-1f62f712aa52

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_OrderReductionProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_MarkedBlowupSequence_MarkedSequenceOfBlowups
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DimensionRecursion
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_IsMaxOrderReduction_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_isMaxOrderReduction_of_forall_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
namespace PrincipalizationRules
private theorem inputLevelData_isMaxOrderReduction (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension)
    (n : ℕ) :
    IsMaxOrderReduction (fun d => d < n) (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed := by
  induction n with
  | zero => exact isMaxOrderReduction_of_forall_not _ (fun m => Nat.not_lt_zero m) _ _
  | succ n ih =>
      have hord : IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed
          (B.inputLevelData n).maxOrderRed :=
        hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
          (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih
          (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih j)
          (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed ih)
      have hmax : IsMaxOrderReduction (fun d => d ≤ n) (B.outputLevelData n).maxOrderRed
          (B.outputLevelData n).orderRed :=
        hB.maxOrderSpec n (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed hord
      exact hmax.mono (fun d => d < n + 1) (fun m hm => Nat.lt_succ_iff.mp hm)
end PrincipalizationRules
end FunctorialResolution.EmbeddedResolution
end
end

set_option autoImplicit false
universe u
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open FunctorialResolution.EmbeddedResolution.PrincipalizationRules
namespace FunctorialResolution.EmbeddedResolution.PrincipalizationRules
theorem _root_.solution (B : PrincipalizationRules.{u}) (hB : B.ReducesInductivelyOnDimension) (n : ℕ) :
    IsOrderReduction (fun d => d ≤ n) (B.outputLevelData n).orderRed (B.inputLevelData n).maxOrderRed :=
  hB.orderSpec n (fun j => B.divisorFamily (B.inputLevelData n).maxOrderRed j)
    (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
    (inputLevelData_isMaxOrderReduction B hB n)
    (fun j => hB.divisorSpec n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n) j)
    (hB.divisorShift n (B.inputLevelData n).maxOrderRed (B.inputLevelData n).orderRed
      (inputLevelData_isMaxOrderReduction B hB n))
end FunctorialResolution.EmbeddedResolution.PrincipalizationRules
