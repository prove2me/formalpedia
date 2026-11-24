-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:35:54.00274+00:00
-- url     : https://prove2.me/submissions/bc3be915-a647-441c-802d-f8d114ddca08

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_bc_X
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_bigCell_szW_szW
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_bigCell_middle_col_vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_bc_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
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



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (szS k r) (szX k r) = diagonal c ∧
    (bigCell k r c μ).submatrix (szX k r) (szX k r) = 0 ∧
    (bigCell k r c μ).submatrix (szW k r) (szX k r) = 0 ∧
    (bigCell k r c μ).submatrix (szX k r) (szW k r) = 0 ∧
    (bigCell k r c μ).submatrix (szW k r) (szW k r) = μ ∧
    (bigCell k r c μ).submatrix (szS k r) (szW k r) = 0 ∧
    (bigCell k r c μ).submatrix (szX k r) (szS k r) = diagonal (fun a => (star (c a))⁻¹) ∧
    (bigCell k r c μ).submatrix (szW k r) (szS k r) = 0 ∧
    (bigCell k r c μ).submatrix (szS k r) (szS k r) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> simp only [submatrix_apply, Matrix.zero_apply]
  · rw [sz_bc_X, diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'; apply h; have := i.isLt; have := j.isLt; rw [Fin.ext_iff] at h'
      simp [szS_val] at h'; exact Fin.ext (by omega)
  · rw [sz_bc_X, if_neg]; intro h; have := i.isLt; rw [Fin.ext_iff] at h; simp [szS_val, szX_val] at h; omega
  · rw [sz_bc_X, if_neg]; intro h; have := j.isLt; rw [Fin.ext_iff] at h; simp [szS_val, szW_val] at h; omega
  · exact bigCell_middle_col_vanish c μ _ (Or.inl (by simp [szX_val])) j
  · exact bigCell_szW_szW c μ i j
  · exact bigCell_middle_col_vanish c μ _ (Or.inr (by have := i.isLt; simp [szS_val]; omega)) j
  · rw [sz_bc_S, diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'; apply h; rw [Fin.ext_iff] at h'; simp [szX_val] at h'; exact Fin.ext h'
  · rw [sz_bc_S, if_neg]; intro h; have := i.isLt; rw [Fin.ext_iff] at h; simp [szW_val, szX_val] at h; omega
  · rw [sz_bc_S, if_neg]; intro h; have := i.isLt; have := j.isLt; rw [Fin.ext_iff] at h
    simp [szS_val, szX_val] at h; omega
end Formalism.FourierDecayAlt.P.SliceLastLevel
