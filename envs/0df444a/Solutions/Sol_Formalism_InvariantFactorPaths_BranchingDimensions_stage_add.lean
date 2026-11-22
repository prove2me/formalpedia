-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.stage_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:29:02.53067+00:00
-- url     : https://prove2.me/submissions/079e4317-fe46-4bdf-bb7e-b16fe519d58c

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
theorem _root_.solution (j l : ℕ) : stage mu (D.n0 + j) l = ent mu (D.n0 + j) (l + j) := by
  simp [Letters.stage]
end Formalism.InvariantFactorPaths.BranchingDimensions
