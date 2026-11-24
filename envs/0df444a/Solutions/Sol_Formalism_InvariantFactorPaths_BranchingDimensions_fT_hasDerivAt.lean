-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.fT_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:12.787144+00:00
-- url     : https://prove2.me/submissions/3ee29f94-d33d-41e2-b9f5-56084a9fe2e4

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
theorem _root_.solution (k' : ℕ) (y : ℝ) (hy : 0 ≤ y) : HasDerivAt (fT k') (fT' k' y) y := by
  have e : fT k' = fun y : ℝ => ∑ j ∈ Icc 1 k', Real.log ((y + j) / j) := rfl
  rw [e]
  unfold fT'
  apply HasDerivAt.fun_sum
  intro j hj
  have hj1 : (0 : ℝ) < j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
  have h1 : HasDerivAt (fun y : ℝ => (y + j) / j) (1 / j) y :=
    ((hasDerivAt_id y).add_const _).div_const _
  have h2 := h1.log (by positivity)
  have e2 : 1 / (y + (j : ℝ)) = 1 / (j : ℝ) / ((y + j) / j) :=
    (div_div_div_cancel_right₀ hj1.ne' _ _).symm
  rw [e2]
  exact h2
end Formalism.InvariantFactorPaths.BranchingDimensions
