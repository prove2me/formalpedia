-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.HStrip.tailPos_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:32:17.525962+00:00
-- url     : https://prove2.me/submissions/9bacc35c-a7df-4cb9-9740-03cdc6d7ea90

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_le_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tail_pos_shift_le

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
    tailPos n b (u + 1) ≤ tailPos n a u := by
  cases n with
  | zero => simp [tailPos]
  | succ k =>
    exact (tail_pos_shift_le a b u k (fun m hm => h.2 m hm)).trans (tailPos_le_succ k a u)
end HStrip
end Formalism.InvariantFactorPaths.BranchingDimensions
