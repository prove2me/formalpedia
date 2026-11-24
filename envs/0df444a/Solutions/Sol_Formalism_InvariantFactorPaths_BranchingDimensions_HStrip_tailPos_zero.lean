-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:10.467499+00:00
-- url     : https://prove2.me/submissions/aff2861e-2020-4838-823f-275c530523a8

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Interl_rev
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_HStrip_tailPos_le
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_wsize_eq_tails

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
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) :
    tailPos n b 0 - tailPos n a 0 ≤ wsize n b - wsize n a := by
  rw [wsize_eq_tails n b, wsize_eq_tails n a]
  have h1 := HStrip.tailPos_le h.rev 0
  linarith
end HStrip
end Formalism.InvariantFactorPaths.BranchingDimensions
