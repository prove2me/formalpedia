-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellDiagonalMap.leviElement_nset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:32.346629+00:00
-- url     : https://prove2.me/submissions/27da4360-f388-4b2c-933d-24350c2cfe91

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellDiagonalMap
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
import Theorems.Thm_Formalism_FourierDecayAlt_P_slice_membership
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
theorem _root_.solution (p : Matrix (Fin j) (Fin j) ℂ) (hp : Formalism.DoubleCosetMeasures.IsUpUni p) : muP k j ρ p ∈ Nset k (j + ρ) := by
  have hdet : p.det ≠ 0 := by rw [Formalism.DoubleCosetMeasures.isUpUni_det ℂ hp]; exact one_ne_zero
  refine ⟨(Formalism.FourierDecayAlt.P.slice_membership k j ρ).2.1 p hdet, ?_, ?_⟩
  · intro a i hai
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, hy⟩ := (eB k j ρ).surjective (eI k (j + ρ) a)
    unfold muP
    rw [← hy, Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    have hv := congrArg Fin.val hy
    have ha := a.isLt
    simp only [eI] at hv
    rw [← hv] at hai
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hv hai
    all_goals first
      | (exfalso; have := x.isLt; have := y.isLt; omega)
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | skip

    simp only [Matrix.fromBlocks_apply₁₁, Sum.inl.injEq]
    rcases eq_or_lt_of_le hai with h | h
    · have : x = y := Fin.ext h.symm
      subst this; simp [hp.2]
    · have hne : x ≠ y := fun e => by subst e; omega
      rw [if_neg hne]
      exact hp.1 (show y < x from h)
  · intro i c hc1 hc2 hi
    obtain ⟨x, rfl⟩ := (eB k j ρ).surjective i
    obtain ⟨y, rfl⟩ := (eB k j ρ).surjective c
    unfold muP
    rw [Ux3.block3_apply]
    simp only [(eB k j ρ).apply_eq_iff_eq]
    rcases x with ((x | x) | x) <;> rcases y with ((y | y) | y) <;>
      simp only [Ux3.block_index_first_val, Ux3.block_index_middle_val, Ux3.block_index_last_val] at hc1 hc2 hi <;>
      first
      | (simp [Matrix.one_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
          Matrix.fromCols_apply_inr]; done)
      | (exfalso; have := x.isLt; have := y.isLt; omega)
end Formalism.FourierDecayAlt.P.BigCellDiagonalMap
