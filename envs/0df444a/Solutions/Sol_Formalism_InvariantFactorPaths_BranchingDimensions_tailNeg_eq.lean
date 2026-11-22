-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tailNeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:42.86186+00:00
-- url     : https://prove2.me/submissions/9ad7da37-48ff-49f7-87e9-ac200c51ba41

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
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailNeg n la u = tailPos n (revW n la) u := rfl
end Formalism.InvariantFactorPaths.BranchingDimensions
