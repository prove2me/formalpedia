-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.weylDim_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:40.570864+00:00
-- url     : https://prove2.me/submissions/f9208f7f-f789-46a2-a46b-1e2ac087e5fb

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
theorem _root_.solution (n : ℕ) (la : ℕ → ℤ) :
    weylDim n la = W n (fun m => (m : ℝ) - (la m : ℝ)) / W n (fun m => (m : ℝ)) := by
  unfold weylDim W
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  push_cast; ring
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
