-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:12.77733+00:00
-- url     : https://prove2.me/submissions/189e09f4-1ead-4f0e-9c20-b358d3824858

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogBinomialProperties

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
theorem _root_.solution (k' : ℕ) : fT k' 0 = 0 := by
  unfold fT
  apply Finset.sum_eq_zero
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  rw [zero_add, div_self hj1.ne', Real.log_one]
end Formalism.InvariantFactorPaths.BranchingDimensions
