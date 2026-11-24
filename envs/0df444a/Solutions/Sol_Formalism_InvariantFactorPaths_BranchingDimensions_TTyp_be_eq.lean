-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.be_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.085376+00:00
-- url     : https://prove2.me/submissions/63f121f0-9088-4b8f-8f5c-6b85eab13484

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (D : Letters) : D.be = D.bePos + D.beNeg := by
  unfold Formalism.InvariantFactorPaths.BranchingDimensions.Letters.be Formalism.InvariantFactorPaths.BranchingDimensions.Letters.bePos Formalism.InvariantFactorPaths.BranchingDimensions.Letters.beNeg
  rw [← Finset.sum_filter_add_sum_filter_not (Icc 1 D.n0) (fun i => D.vec i = true)]
  simp only [Bool.not_eq_true]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
