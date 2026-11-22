-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.apply_le_of_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:16.208336+00:00
-- url     : https://prove2.me/submissions/730426de-90ca-4e8d-9f55-6084803e0655

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution (M : Matrix ι ι ℂ)
    (hM : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤ 1)
    (z : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin M z‖ ≤ ‖z‖ := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm z
  calc ‖Matrix.toEuclideanLin M z‖
      ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ * ‖z‖ := h
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg z)
    _ = ‖z‖ := one_mul _
end Formalism.BranchingDeterminantCap.PrismTransfer
