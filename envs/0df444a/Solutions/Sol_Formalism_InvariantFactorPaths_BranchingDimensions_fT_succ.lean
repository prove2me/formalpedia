-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:41.668182+00:00
-- url     : https://prove2.me/submissions/2f1d9f25-c0f5-4761-abf0-b144d6d2b221

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties

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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (k' : ℕ) (y : ℝ) :
    fT (k' + 1) y = fT k' y + Real.log ((y + ((k' + 1 : ℕ) : ℝ)) / ((k' + 1 : ℕ) : ℝ)) := by
  unfold fT
  rw [Finset.sum_Icc_succ_top (by omega)]
end Formalism.InvariantFactorPaths.BranchingDimensions
