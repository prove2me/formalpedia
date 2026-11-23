-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.opNormAt_rowMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:28.220656+00:00
-- url     : https://prove2.me/submissions/4cbb356f-9615-4895-a349-99e1589ab28f

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_row_norm_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_mul_blockDiag_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_toMatrix_rowMap

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
theorem _root_.solution {n : ℕ} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (G : ℕ) (x : Fin n → V →ₗ[K] V) (v : InfinitePlace K)
    (hx : ∀ i, opNormAt b X b X v (x i) ≤ 1) :
    opNormAt (Pi.basis fun _ : Fin n => b) (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X v
      (rowMap ((G : K) ^ 3) x) ≤ (G : ℝ) ^ 3 * Real.sqrt n := by
  dsimp only [opNormAt]
  refine row_norm_le (fun i => (X v)⁻¹ * (LinearMap.toMatrix b b (x i)).map v.embedding * X v)
    ((G : ℝ) ^ 3) (by positivity) hx _ ?_
  intro k p
  obtain ⟨i, j⟩ := p
  dsimp only
  rw [mul_blockDiag_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, toMatrix_rowMap, map_mul, map_pow, map_natCast,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring
end Formalism.BranchingDeterminantCap.PrismTransfer
