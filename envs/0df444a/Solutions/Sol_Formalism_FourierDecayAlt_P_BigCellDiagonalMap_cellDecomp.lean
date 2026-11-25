-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellDiagonalMap.cellDecomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:16:32.348512+00:00
-- url     : https://prove2.me/submissions/4014a47b-5d9b-4274-807e-2c92ea872ed6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_leviElement_mul_mMap
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_leviElement_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_muOf_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_mMap_diag
import Theorems.Thm_Formalism_FourierDecayAlt_P_BigCellDiagonalMap_dmin_lead
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x9_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_bigCell_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_gv_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_rn_nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_mMap_mul_muP
import Theorems.Thm_Formalism_FourierDecayAlt_P_hat_z_minimum_degree
import Theorems.Thm_Formalism_FourierDecayAlt_P_hat_z_on_slice
import Theorems.Thm_Formalism_FourierDecayAlt_P_ldu_decomposition_exists
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_mem_n_mul
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
theorem _root_.solution : BigCellDecomposition.CellDecomp := by
  intro k r z z' g hg hD
  have hDl : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead (Zh k r 0 g) l hl ≠ 0 := fun l hl => by
    rw [← dmin_lead z z' g l hl]; exact hD ⟨l, by omega⟩ hl
  have hDj : DjU k r 0 g ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.hat_z_minimum_degree k r 0 z z' g
    rw [← h]; exact hD ⟨r, by omega⟩ le_rfl
  obtain ⟨x, x', Z, γ, _hZ, hγ, hgeq⟩ := Ux3.bigCell_exists (k := k) (j := r) (ρ := 0) g hg hDj
  have hZh : Zh k r 0 g = Z := by rw [hgeq]; exact Formalism.FourierDecayAlt.P.hat_z_on_slice k r 0 x x' Z γ
  have hDZ : ∀ (l : ℕ) (hl : l ≤ r), Formalism.FourierDecayAlt.S3.lead Z l hl ≠ 0 := by rw [← hZh]; exact hDl
  obtain ⟨L, U, d, hL, hU, hLDU, hlead⟩ :=
    Formalism.FourierDecayAlt.P.ldu_decomposition_exists ℂ r Z (fun l hl => (hDZ l hl.le).isUnit)
  have hd : ∀ a, d a ≠ 0 := fun a h0 => by
    have h1 := hlead a.val a.isLt
    rw [h0, zero_mul] at h1
    exact hDZ (a.val + 1) a.isLt h1
  have hLh : Formalism.DoubleCosetMeasures.IsUpUni Lᴴ := by
    refine ⟨fun i j hij => ?_, fun a => ?_⟩
    · rw [Matrix.conjTranspose_apply, hL.1 hij, star_zero]
    · rw [Matrix.conjTranspose_apply, hL.2 a, star_one]
  have hLu : IsUnit L.det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det ℂ hL]; exact isUnit_one
  have hLhu : IsUnit Lᴴ.det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hLh]; exact isUnit_one
  have hP : muP k r 0 Lᴴ ∈ Nset k (r + 0) := leviElement_nset _ hLh
  have hPu : IsUnit (muP k r 0 Lᴴ).det := Ux3.gv_det hP.1
  have h1 : muP k r 0 Lᴴ * mMap k r 0 Z γ = mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U := by
    rw [leviElement_mul_mMap _ _ _ hLhu, Ux4.mMap_mul_muP, hLDU, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hLu, Matrix.one_mul]
  have key : mMap k r 0 Z γ = (muP k r 0 Lᴴ)⁻¹ * (mMap k r 0 (Matrix.diagonal d) γ * muP k r 0 U) := by
    rw [← h1, Matrix.nonsing_inv_mul_cancel_left _ _ hPu]
  refine ⟨muP k r 0 Lᴴ * Rn k r 0 x, WeylGroupFacts.mem_n_mul hP (Ux3.rn_nset x),
    muP k r 0 U * Rn k r 0 x', WeylGroupFacts.mem_n_mul (leviElement_nset _ hU) (Ux3.rn_nset x'), d, hd, muOf γ, muOf_mem γ hγ, ?_⟩
  rw [hgeq, key, ← mMap_diag r d hd γ, Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.BigCellDiagonalMap
