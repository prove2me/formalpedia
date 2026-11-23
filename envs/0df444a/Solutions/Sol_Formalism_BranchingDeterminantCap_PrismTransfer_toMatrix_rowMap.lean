-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_rowMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:23.418829+00:00
-- url     : https://prove2.me/submissions/499c349d-1600-479a-b2c5-a178a0ea34ef

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap_apply

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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix (Pi.basis fun _ : Fin n => b) b (rowMap c x) k ⟨i, j⟩ =
      c * LinearMap.toMatrix b b (x i) k j := by
  have h : rowMap c x ((Pi.basis fun _ : Fin n => b) ⟨i, j⟩) = c • x i (b j) := by
    rw [rowMap_apply, Finset.sum_eq_single i]
    · simp [Pi.basis_apply]
    · intro i' _ hi'
      simp [Pi.basis_apply, hi']
    · simp
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, h]
  simp
end Formalism.BranchingDeterminantCap.PrismTransfer
