-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.blockDiag_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:21.550961+00:00
-- url     : https://prove2.me/submissions/1157742e-94d4-4010-a440-d255f2a0b5da

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_mul_inv

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
    (Matrix.blockDiagonal' (fun _ : Fin n => Y))⁻¹ = Matrix.blockDiagonal' (fun _ : Fin n => Y⁻¹) := Matrix.inv_eq_right_inv (blockDiag_mul_inv Y hY)
end Formalism.BranchingDeterminantCap.PrismTransfer
