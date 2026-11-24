-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Branch.det_diff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:28.877631+00:00
-- url     : https://prove2.me/submissions/f932783f-8640-447a-8e1d-c036d13de347

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_Branch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Formalism.InvariantFactorPaths.BranchingDimensions.Branch
namespace Formalism.InvariantFactorPaths.BranchingDimensions.Branch
theorem _root_.solution {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (h : ∀ i, M i 0 = 1) :
    M.det = (Matrix.of fun i j : Fin n => M i.succ j.succ - M i.castSucc j.succ).det := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
    Matrix.of fun i j => Fin.cases (M 0 j) (fun i' => M i'.succ j - M i'.castSucc j) i
  have h1 : M.det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1) (fun j => ?_) (fun i j => ?_)
    · simp [B]
    · simp [B]
  rw [h1, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h2 : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i; simp [B, h]
  have h3 : B 0 0 = 1 := by simp [B, h]
  simp only [h2, h3, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  congr 1
end Formalism.InvariantFactorPaths.BranchingDimensions.Branch
