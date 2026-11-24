-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Interl.tailPos_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:22.056852+00:00
-- url     : https://prove2.me/submissions/636bbcb9-f87d-463a-bdd1-b48bbca8a85b

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_tailPos_le_succ
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
namespace Interl
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) (u : ℕ) :
    tailPos n a u ≤ tailPos (n + 1) b u :=
  (tailPos_mono (fun m hm => (h m hm).1) u).trans (tailPos_le_succ n b u)
end Interl
end Formalism.InvariantFactorPaths.BranchingDimensions
