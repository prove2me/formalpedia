-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.W_extW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:15.944735+00:00
-- url     : https://prove2.me/submissions/4d6977b0-7989-4a61-9edc-931a805116b8

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_det_vandermonde_eq_vandermondeProd
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_extW_val

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
theorem _root_.solution {n : ℕ} (la : Fin n → ℤ) :
    W n (fun m => (m : ℝ) - (extW la m : ℝ)) = (Matrix.vandermonde fun i : Fin n => (i : ℝ) - (la i : ℝ)).det := by
  rw [← det_vandermonde_eq_vandermondeProd]
  simp only [extW_val]
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
