-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.sigma_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:08.150249+00:00
-- url     : https://prove2.me/submissions/52e65a2c-4ddd-4a4b-a7ef-3dedcef5142b

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
theorem _root_.solution {n : ℕ} (z : EuclideanSpace ℂ (Σ _ : Fin n, ι)) :
    ‖z‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (fun j => z ⟨i, j⟩) : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  try rfl
end Formalism.BranchingDeterminantCap.PrismTransfer
