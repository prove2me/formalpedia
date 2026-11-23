-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.col_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:21.925479+00:00
-- url     : https://prove2.me/submissions/24c4fbe0-c307-4b41-851b-1cd7ed078657

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_sigma_norm_sq
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_apply_le_of_norm_le

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
theorem _root_.solution {n : ℕ} (M : Fin n → Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ i, ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M i))‖ ≤ 1)
    (C : Matrix (Σ _ : Fin n, ι) ι ℂ) (hC : ∀ p k, C p k = (c : ℂ) * M p.1 p.2 k) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C)‖ ≤ c * Real.sqrt n := by
  have hsq : 0 ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hsq fun z => ?_
  have hblk : ∀ i, (WithLp.toLp 2 (fun j =>
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z) ⟨i, j⟩) : EuclideanSpace ℂ ι) =
      (c : ℂ) • Matrix.toEuclideanLin (M i) z := by
    intro i
    ext j
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, hC, Finset.mul_sum, mul_assoc]
  have hsq2 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z‖ ^ 2 ≤
      (c * Real.sqrt n * ‖z‖) ^ 2 := by
    rw [sigma_norm_sq]
    simp only [hblk]
    calc ∑ i, ‖(c : ℂ) • Matrix.toEuclideanLin (M i) z‖ ^ 2
        ≤ ∑ _i : Fin n, (c * ‖z‖) ^ 2 := by
          gcongr with i
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (apply_le_of_norm_le (M i) (hM i) z) hc
      _ = (c * Real.sqrt n * ‖z‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          calc (n : ℝ) * (c * ‖z‖) ^ 2 = (c * ‖z‖) ^ 2 * (Real.sqrt n) ^ 2 := by rw [hs]; ring
            _ = (c * Real.sqrt n * ‖z‖) ^ 2 := by ring
  have hy : 0 ≤ c * Real.sqrt n * ‖z‖ := mul_nonneg hsq (norm_nonneg z)
  nlinarith [norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z)]
end Formalism.BranchingDeterminantCap.PrismTransfer
