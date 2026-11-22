-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.actV_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:38.475342+00:00
-- url     : https://prove2.me/submissions/f30874ed-b416-4bb4-b808-4b546d73b62f

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
theorem _root_.solution {l : ℕ} : actV D l = true ↔ l ≤ D.n0 ∧ D.vec l = true := by
  simp [actV]
end Formalism.InvariantFactorPaths.BranchingDimensions
