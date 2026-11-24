-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.stLen_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:13.019799+00:00
-- url     : https://prove2.me/submissions/bfa354f1-0404-430c-a06a-4fb39bf674aa

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
variable {D : Letters} {mu : D.Stages}
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (j : ℕ) : D.stLen (D.n0 + j) = D.k - j := by
  unfold Letters.stLen
  rw [Nat.add_sub_cancel_left]
end Formalism.InvariantFactorPaths.BranchingDimensions
