-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.finsum_prop_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:40.963506+00:00
-- url     : https://prove2.me/submissions/f7435488-2ac7-4e37-b7de-12ea1dd2f640

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution {α : Type*} {p q : α → Prop} {f g : α → ℝ} (h : ∀ y, p y ↔ q y)
    (hf : ∀ y, q y → f y = g y) : ∑ᶠ (y : α) (_ : p y), f y = ∑ᶠ (y : α) (_ : q y), g y := by
  classical
  refine finsum_congr fun y => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases hq : q y
  · rw [if_pos ((h y).2 hq), if_pos hq, hf y hq]
  · rw [if_neg (fun hp => hq ((h y).1 hp)), if_neg hq]
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
