-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.sum_ite_const_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:17.80936+00:00
-- url     : https://prove2.me/submissions/2db584e2-7833-4615-915b-44d47c03c745

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution {n Ns : ℕ} (p : ℕ → Prop) [DecidablePred p]
    (hc : ((range n).filter p).card ≤ Ns) {c : ℝ} (h0 : 0 ≤ c) :
    ∑ i ∈ range n, (if p i then c else 0) ≤ (Ns : ℝ) * c := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) h0
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
