-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.actC_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:41.262437+00:00
-- url     : https://prove2.me/submissions/2bef913a-4a73-4e68-b19f-70efbeaa7314

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
theorem _root_.solution {l : ℕ} : actC D l = true ↔ l ≤ D.n0 ∧ D.vec l = false := by
  simp [actC]
end Formalism.InvariantFactorPaths.BranchingDimensions
