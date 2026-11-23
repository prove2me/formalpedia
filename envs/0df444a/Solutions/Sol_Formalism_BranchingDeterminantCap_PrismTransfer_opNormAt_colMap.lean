-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.opNormAt_colMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:30.730057+00:00
-- url     : https://prove2.me/submissions/33867674-278a-4daf-8b3b-5cb59278aaf6

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_col_norm_le
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_inv
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_blockDiag_mul_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_toMatrix_colMap

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
    (hX : ∀ v, IsUnit (X v).det) (G : ℕ) (x : Fin n → V →ₗ[K] V) (v : InfinitePlace K)
    (hx : ∀ i, opNormAt b X b X v (x i) ≤ 1) :
    opNormAt b X (Pi.basis fun _ : Fin n => b) (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v
      (colMap ((G : K) ^ 3) x) ≤ (G : ℝ) ^ 3 * Real.sqrt n := by
  dsimp only [opNormAt]
  rw [blockDiag_inv (X v) (hX v)]
  refine col_norm_le (fun i => (X v)⁻¹ * (LinearMap.toMatrix b b (x i)).map v.embedding * X v)
    ((G : ℝ) ^ 3) (by positivity) hx _ ?_
  intro p k
  obtain ⟨i, j⟩ := p
  dsimp only
  conv_lhs => rw [Matrix.mul_apply]
  simp only [blockDiag_mul_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, toMatrix_colMap, map_mul, map_pow, map_natCast,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring
end Formalism.BranchingDeterminantCap.PrismTransfer
