-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.latestC_frame
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:42.398838+00:00
-- url     : https://prove2.me/submissions/b8448582-b9cd-4da9-9354-2d9bac0557af

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
theorem _root_.solution (i j : ℕ) (hi : D.n0 ≤ i) (hj : D.n0 ≤ j) : D.latestC i = D.latestC j := by
  unfold Letters.latestC
  rw [min_eq_right hi, min_eq_right hj]
end Formalism.InvariantFactorPaths.BranchingDimensions
