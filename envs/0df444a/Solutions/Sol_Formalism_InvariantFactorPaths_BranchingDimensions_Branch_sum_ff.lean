-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.sum_ff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:07:21.953116+00:00
-- url     : https://prove2.me/submissions/d5da9ccb-05c4-453a-bc56-44d4eb584b76

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_ff_diff
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_Branch_sum_Ico_int_sub

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
theorem _root_.solution (j : ℕ) (c : ℝ) (a b : ℤ) (h : a ≤ b) :
    ((j : ℝ) + 1) * ∑ x ∈ Icc a b, ff j (c - (x : ℝ)) =
      ff (j + 1) (c + 1 - (a : ℝ)) - ff (j + 1) (c - (b : ℝ)) := by
  have := sum_Ico_int_sub (fun x => - ff (j + 1) (c + 1 - (x : ℝ))) a (b + 1) (by omega)
  rw [Finset.Ico_add_one_right_eq_Icc] at this
  rw [Finset.mul_sum]
  have e : ∀ x ∈ Icc a b, ((j : ℝ) + 1) * ff j (c - (x : ℝ)) =
      - ff (j + 1) (c + 1 - ((x + 1 : ℤ) : ℝ)) - - ff (j + 1) (c + 1 - (x : ℝ)) := by
    intro x _
    rw [← ff_diff]
    push_cast
    have e1 : c + 1 - ((x : ℝ) + 1) = c - x := by ring
    have e2 : c + 1 - (x : ℝ) = c - x + 1 := by ring
    rw [e1, e2]; ring
  rw [Finset.sum_congr rfl e, this]
  push_cast
  have e1 : c + 1 - ((b : ℝ) + 1) = c - b := by ring
  rw [e1]; ring
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
