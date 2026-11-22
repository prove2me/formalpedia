-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:51.27805+00:00
-- url     : https://prove2.me/submissions/a590a1e0-42d4-4171-8db1-675149038bff

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
theorem _root_.solution {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    Matrix.blockDiagonal' (fun _ : Fin n => Y) * Matrix.blockDiagonal' (fun _ : Fin n => Y⁻¹) = 1 := by
  rw [← Matrix.blockDiagonal'_mul]
  have h : (fun _ : Fin n => Y * Y⁻¹) = fun _ : Fin n => (1 : Matrix ι ι ℂ) := by
    funext _
    exact Matrix.mul_nonsing_inv Y hY
  rw [h]
  exact Matrix.blockDiagonal'_one
end Formalism.BranchingDeterminantCap.PrismTransfer
