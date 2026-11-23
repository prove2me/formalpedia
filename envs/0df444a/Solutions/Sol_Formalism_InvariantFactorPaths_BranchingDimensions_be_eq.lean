-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.be_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:40.207404+00:00
-- url     : https://prove2.me/submissions/4a86b7ef-4d01-4f9c-93a3-65cf4f850c9c

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
theorem _root_.solution (D : Letters) : D.be = D.bePos + D.beNeg := by
  unfold Letters.be Letters.bePos Letters.beNeg
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
  congr 2
  ext i
  simp
end Formalism.InvariantFactorPaths.BranchingDimensions
