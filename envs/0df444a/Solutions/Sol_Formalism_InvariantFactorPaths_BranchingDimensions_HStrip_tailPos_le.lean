-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:16.390827+00:00
-- url     : https://prove2.me/submissions/d898b0dc-ff89-4c50-9fb5-99d610739dc1

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_mono

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
namespace HStrip
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u := tailPos_mono h.1 u
end HStrip
end Formalism.InvariantFactorPaths.BranchingDimensions
