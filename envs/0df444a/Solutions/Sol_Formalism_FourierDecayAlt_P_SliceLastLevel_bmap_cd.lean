-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.bmap_cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:58:49.475569+00:00
-- url     : https://prove2.me/submissions/12d5ea79-d2f3-4cbd-af1a-83da9d2d3927

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_cd_bmap_entry_c
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_cd_bmap_entry_ci
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_cdm_iff
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
open Matrix Filter Topology
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O) (hx : ∀ x ∈ O, ∀ a, cx x a ≠ 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bmap k r cx μx) O := by
  rw [Formalism.FourierDecayAlt.P.Ux10.cdm_iff]
  intro i j
  have hμe := Formalism.FourierDecayAlt.P.Ux10.cdm_iff.1 hμx
  unfold bmap bigCell
  by_cases hj : j.val < r
  · simp only [hj, dif_pos]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · simp only [hi, if_true]
      exact cd_bmap_entry_c hcx _
    · simp only [hi, if_false]
      exact contDiffOn_const
  · simp only [hj, dif_neg, not_false_eq_true]
    by_cases hj2 : j.val ≤ r + k
    · simp only [hj2, dif_pos]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [hi, dif_pos, and_self]
        unfold castW
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
        exact hμe _ _
      · simp only [hi, dif_neg, not_false_eq_true]
        exact contDiffOn_const
    · simp only [hj2, dif_neg, not_false_eq_true]
      by_cases hi : i.val = 2 * r + k - j.val
      · simp only [hi, if_true]
        exact cd_bmap_entry_ci hcx hx _
      · simp only [hi, if_false]
        exact contDiffOn_const
end Formalism.FourierDecayAlt.P.SliceLastLevel
