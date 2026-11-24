-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:34:10.434191+00:00
-- url     : https://prove2.me/submissions/fca54ac5-d451-4a5c-bbda-0abbac440552

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Hpk_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x8_Hpk_sq
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_eq_sig_iff
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sgn_sig
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
theorem _root_.solution {q : B.Mat k r} (hq : q ∈ B.GV k r) (i j : Fin (2 * r + k + 1)) :
    q⁻¹ i j = Formalism.QuantumDeterminants.GBasic.sgn k r i * Formalism.QuantumDeterminants.GBasic.sgn k r j *
      star (q (Formalism.QuantumDeterminants.GBasic.sig k r j) (Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  have h1 : (Hpk k r * qᴴ * Hpk k r) * q = 1 := by
    have hq' : qᴴ * Hpk k r * q = Hpk k r := hq
    calc (Hpk k r * qᴴ * Hpk k r) * q = Hpk k r * (qᴴ * Hpk k r * q) := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * Hpk k r := by rw [hq']
      _ = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  rw [Matrix.inv_eq_left_inv h1]
  simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.GBasic.Hpk_eq, conjTranspose_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Formalism.QuantumDeterminants.GBasic.eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Formalism.QuantumDeterminants.GBasic.sgn_sig]
  ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
