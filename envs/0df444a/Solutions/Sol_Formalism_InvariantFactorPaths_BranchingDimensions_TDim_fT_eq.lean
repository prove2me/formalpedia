-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.fT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:29.838923+00:00
-- url     : https://prove2.me/submissions/b74ab949-8d63-4dcb-bbdb-a71b8b88c23d

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution (k' : ℕ) (z : ℝ) : fT k' z = ∑ d ∈ Icc 1 k', hh z d := rfl
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
