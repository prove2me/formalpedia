-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.latest_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:42.862582+00:00
-- url     : https://prove2.me/submissions/4f5bca14-47f8-4623-b2c3-139e3bb16e06

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
theorem _root_.solution (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) :
    (((List.range' 1 (i + 1)).filter q).reverse).map B =
      if q (i + 1) = true then B (i + 1) :: (((List.range' 1 i).filter q).reverse).map B
      else (((List.range' 1 i).filter q).reverse).map B := by
  by_cases hq : q (i + 1) = true
  · simp [List.range'_concat, List.filter_append, hq, add_comm]
  · simp [List.range'_concat, List.filter_append, hq, add_comm]
end Formalism.InvariantFactorPaths.BranchingDimensions
