-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_gblocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:11.398185+00:00
-- url     : https://prove2.me/submissions/5402a9cb-d896-4248-8cf1-693554af630e

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_mul_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_subN
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_sz_bc
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
theorem _root_.solution {m p : B.Mat k r} (hm : m ∈ Nset k r) (hp : p ∈ Nset k r) (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (m * bigCell k r c μ * p).submatrix (szS k r) (szX k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szS k r) (szW k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szW k r) ∧
    (m * bigCell k r c μ * p).submatrix (szS k r) (szS k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szS k r) ∧
    (m * bigCell k r c μ * p).submatrix (szW k r) (szX k r) =
        m.submatrix (szW k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szX k r) (szX k r) =
        m.submatrix (szX k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szW k r) (szW k r) =
        m.submatrix (szW k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szW k r) + μ := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := sz_bc (k := k) c μ
  obtain ⟨m1, m2, m3, m4⟩ := sz_subN hm
  obtain ⟨p1, p2, p3, p4⟩ := sz_subN hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sz_mul_sub, b1, b2, b3, b4, b5, b6, b7, b8, b9, m1, m2, m3, m4, p1, p2, p3, p4, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  exact add_comm _ _
end Formalism.FourierDecayAlt.P.SliceLastLevel
