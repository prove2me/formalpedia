-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tailPos_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:53:59.709625+00:00
-- url     : https://prove2.me/submissions/32fdd366-b836-457f-88ee-60c539d8baf4

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_succ

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
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailPos n la u ≤ tailPos (n + 1) la u := by
  rw [tailPos_succ]
  split_ifs
  · linarith [le_max_right (la n) 0]
  · linarith
end Formalism.InvariantFactorPaths.BranchingDimensions
