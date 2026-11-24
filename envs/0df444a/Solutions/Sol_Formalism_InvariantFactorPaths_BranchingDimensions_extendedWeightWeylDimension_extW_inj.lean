-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.extW_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:32:31.784492+00:00
-- url     : https://prove2.me/submissions/a72e846b-a3ae-4d1f-be4a-b904b6ca57ad

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_extW_val

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
theorem _root_.solution {n : ℕ} {a b : Fin n → ℤ} (h : ∀ m, m < n → extW a m = extW b m) : a = b := by
  funext m
  rw [← extW_val a m, ← extW_val b m]
  exact h _ m.2
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
