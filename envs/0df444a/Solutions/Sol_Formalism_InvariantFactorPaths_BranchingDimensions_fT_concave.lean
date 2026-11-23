-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_concave
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:41.331696+00:00
-- url     : https://prove2.me/submissions/bb6b09dc-9f0c-4bd1-8e0c-885d5e52b8bf

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
theorem _root_.solution (k' : ℕ) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    fT k' x - fT k' y ≤ fT' k' y * (x - y) := by
  unfold fT fT'
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hxj : 0 < x + j := by linarith
  have hyj : 0 < y + j := by linarith
  rw [← Real.log_div (by positivity) (by positivity)]
  have e : (x + j) / j / ((y + j) / j) = (x + j) / (y + j) := by field_simp
  rw [e]
  refine le_trans (Real.log_le_sub_one_of_pos (by positivity)) (le_of_eq ?_)
  field_simp
  ring
end Formalism.InvariantFactorPaths.BranchingDimensions
