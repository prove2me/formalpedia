-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.row_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:24:36.176431+00:00
-- url     : https://prove2.me/submissions/25f67b01-37cf-4752-838a-f8ea0df0447d

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
    (R : Matrix ι (Σ _ : Fin n, ι) ℂ) (hR : ∀ k p, R k p = (c : ℂ) * M p.1 k p.2) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ ≤ c * Real.sqrt n := by
  have hsq : 0 ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hsq fun z => ?_
  let zs : Fin n → EuclideanSpace ℂ ι := fun i => WithLp.toLp 2 (fun j => z ⟨i, j⟩)
  have hdec : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R) z =
      ∑ i, (c : ℂ) • Matrix.toEuclideanLin (M i) (zs i) := by
    ext k
    simp [zs, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sigma, hR,
      Finset.mul_sum, mul_assoc, Finset.sum_apply]
  have hnorm : ∑ i, ‖zs i‖ ^ 2 = ‖z‖ ^ 2 := (sigma_norm_sq z).symm
  have hzs : ∑ i, ‖zs i‖ ≤ Real.sqrt n * ‖z‖ := by
    have hcs : (∑ i, ‖zs i‖) ^ 2 ≤ (Finset.univ : Finset (Fin n)).card * ∑ i, ‖zs i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_univ, Fintype.card_fin, hnorm] at hcs
    have h0 : 0 ≤ ∑ i, ‖zs i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [← Real.sqrt_sq h0, ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hcs
  rw [hdec]
  calc ‖∑ i, (c : ℂ) • Matrix.toEuclideanLin (M i) (zs i)‖
      ≤ ∑ i, ‖(c : ℂ) • Matrix.toEuclideanLin (M i) (zs i)‖ := norm_sum_le _ _
    _ = ∑ i, c * ‖Matrix.toEuclideanLin (M i) (zs i)‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
    _ ≤ ∑ i, c * ‖zs i‖ := by
        gcongr with i
        exact apply_le_of_norm_le (M i) (hM i) (zs i)
    _ = c * ∑ i, ‖zs i‖ := by rw [Finset.mul_sum]
    _ ≤ c * (Real.sqrt n * ‖z‖) := by gcongr
    _ = c * Real.sqrt n * ‖z‖ := by ring
end Formalism.BranchingDeterminantCap.PrismTransfer
