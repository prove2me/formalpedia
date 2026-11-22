-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.stage_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:58.722667+00:00
-- url     : https://prove2.me/submissions/a009e400-d983-4a06-93af-37d420fef495

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
theorem _root_.solution (i : ℕ) (h : i ≤ D.n0) : stage mu i = ent mu i := by
  funext l
  simp [Letters.stage, Nat.sub_eq_zero_of_le h]
end Formalism.InvariantFactorPaths.BranchingDimensions
