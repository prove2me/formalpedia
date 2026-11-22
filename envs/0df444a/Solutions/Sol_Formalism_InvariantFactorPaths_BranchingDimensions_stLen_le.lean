-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.stLen_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:38.109115+00:00
-- url     : https://prove2.me/submissions/151cb91c-66c6-45d4-9f80-974a88610f24

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
theorem _root_.solution (i : ℕ) (h : i ≤ D.n0) : D.stLen i = D.k := by
  unfold Letters.stLen
  rw [Nat.sub_eq_zero_of_le h, Nat.sub_zero]
end Formalism.InvariantFactorPaths.BranchingDimensions
