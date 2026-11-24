-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.W_id_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:28.938019+00:00
-- url     : https://prove2.me/submissions/a80ece81-0977-413f-ba42-de6a16e3a876

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch

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
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution (n : ℕ) : W n (fun m => (m : ℝ)) ≠ 0 := by
  unfold W
  refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i hi => ?_
  have : (i : ℝ) < j := by exact_mod_cast Finset.mem_range.1 hi
  exact sub_ne_zero.2 this.ne'
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
