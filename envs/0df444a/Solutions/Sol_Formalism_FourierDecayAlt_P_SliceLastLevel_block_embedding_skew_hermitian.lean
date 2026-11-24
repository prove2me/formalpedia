-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.block_embedding_skew_hermitian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:29:41.18781+00:00
-- url     : https://prove2.me/submissions/8800db5a-2c1a-42c8-be7c-a2ce8e6d6406

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_castW_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_castW_ct
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_hb_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_SliceLastLevel_tr_castW_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_Hpk
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_EmT_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_conjT
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_Em
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
open Matrix MeasureTheory Filter Topology
set_option linter.style.haveILetI false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {Y : B.Mat k 0} (hY : B.inLie k 0 Y) : B.inLie k r (emb0 k r Y) := by
  have hY' : Yᴴ * Hpk k 0 + Hpk k 0 * Y = 0 := hY
  have hc : (castW Y)ᴴ * Hb k + Hb k * castW Y = 0 := by
    rw [tr_hb_eq, tr_castW_ct, ← tr_castW_mul, ← tr_castW_mul, ← tr_castW_add, hY', tr_castW_zero]
  show (emb0 k r Y)ᴴ * Hpk k r + Hpk k r * emb0 k r Y = 0
  rw [levelEmbed_eq_conj_cast, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, P.B2x3.EmT_conjT, P.B2x3.Em_conjT]
  calc P.B2x3.Em k r * ((castW Y)ᴴ * (P.B2x3.Em k r)ᵀ) * Hpk k r +
        Hpk k r * (P.B2x3.Em k r * castW Y * (P.B2x3.Em k r)ᵀ)
      = P.B2x3.Em k r * (castW Y)ᴴ * ((P.B2x3.Em k r)ᵀ * Hpk k r) +
        (Hpk k r * P.B2x3.Em k r) * castW Y * (P.B2x3.Em k r)ᵀ := by simp only [Matrix.mul_assoc]
    _ = P.B2x3.Em k r * ((castW Y)ᴴ * Hb k + Hb k * castW Y) * (P.B2x3.Em k r)ᵀ := by
        rw [P.B2x3.EmT_Hpk, P.B2x3.Hpk_Em]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hc, Matrix.mul_zero, Matrix.zero_mul]
end Formalism.FourierDecayAlt.P.SliceLastLevel
