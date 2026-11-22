-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.extW_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:28.187684+00:00
-- url     : https://prove2.me/submissions/9b89ab0c-cd40-48fe-9f4d-b49e54a98443

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch

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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution {n : ℕ} (la : Fin n → ℤ) (i : Fin n) : extW la i.val = la i := by
  simp [extW]
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
