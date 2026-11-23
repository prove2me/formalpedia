-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.mul_blockDiag_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:22.132259+00:00
-- url     : https://prove2.me/submissions/af4708e0-e7fd-4431-96f1-aa84d31a3e36

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
theorem _root_.solution {n : ℕ} {κ : Type} (N : Matrix κ (Σ _ : Fin n, ι) ℂ) (Y : Matrix ι ι ℂ)
    (k : κ) (i : Fin n) (j : ι) :
    (N * Matrix.blockDiagonal' (fun _ : Fin n => Y)) k ⟨i, j⟩ = ∑ l, N k ⟨i, l⟩ * Y l j := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun l _ => by rw [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.blockDiagonal'_apply_ne _ _ _ hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
end Formalism.BranchingDeterminantCap.PrismTransfer
