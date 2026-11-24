-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellDiagonalMap.mMap_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:32.915806+00:00
-- url     : https://prove2.me/submissions/f5e46ee9-4e78-402a-8fb9-461d2bf2c126

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_inv_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_first_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_last_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block_index_middle_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll



set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellDiagonalMap
variable {k j ρ : ℕ}
namespace Formalism.FourierDecayAlt.P.BigCellDiagonalMap
theorem _root_.solution (r : ℕ) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ : B.Mat k 0) :
    (mMap k r 0 (Matrix.diagonal d) γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      bigCell k r d (muOf γ) := by
  ext i l
  obtain ⟨x, rfl⟩ := (eB k r 0).surjective i
  obtain ⟨y, rfl⟩ := (eB k r 0).surjective l
  unfold mMap
  rw [Matrix.diagonal_conjTranspose, inv_diag (star d) (fun a => by simpa [Pi.star_apply] using hd a), Ux3.block3_apply]
  have v1 := @Ux3.block_index_first_val k r 0
  have v2 := @Ux3.block_index_middle_val k r 0
  have v3 := @Ux3.block_index_last_val k r 0
  rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
    simp only [bigCell, v1, v2, v3, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply]
  all_goals
    have hx := x.isLt
    have hy := y.isLt
    simp only [Fin.ext_iff, v1, v2, v3, esI, G.wMat, Matrix.of_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Ring.inverse_eq_inv', Pi.star_apply, Fin.val_rev, Pi.inv_apply, Complex.star_def, mul_one,
      one_mul, mul_zero, zero_mul]
    split_ifs <;> first
      | rfl
      | (exfalso; omega)
      | (congr 1; ext; simp only [Fin.val_mk]; omega)
      | (congr 2; ext; simp only [Fin.val_mk]; omega)
      | (intro h; exfalso; omega)
      | (simp; done)
      | (simp only [mul_one]; congr 3; ext; simp only [Fin.val_mk]; omega)
      | (simp only [muOf, eW, Matrix.reindex_apply, Matrix.submatrix_apply]; congr 1 <;> (ext; simp))
      | skip
end Formalism.FourierDecayAlt.P.BigCellDiagonalMap
