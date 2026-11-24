-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.pow_trade
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:10:21.621286+00:00
-- url     : https://prove2.me/submissions/95af8313-9d75-44f6-9acd-0fd472fb7ae7

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {G P C a b e : ℝ} (hG : 1 ≤ G) (hP : 0 < P) (hC : 1 ≤ C) (ha : 0 ≤ a) (_he : 0 ≤ e)
    (hPb : P ≤ C ^ (3 : ℝ) * G ^ e) (hab : e * a ≤ b) :
    G ^ (-b) ≤ C ^ (3 * a) * P ^ (-a) := by
  have hG0 : 0 < G := lt_of_lt_of_le one_pos hG
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have h1 : G ^ (-b) ≤ G ^ (-(e * a)) := Real.rpow_le_rpow_of_exponent_le hG (by linarith)
  have h2 : P ^ a ≤ (C ^ (3 : ℝ) * G ^ e) ^ a := Real.rpow_le_rpow hP.le hPb ha
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC0.le, ← Real.rpow_mul hG0.le] at h2
  have h3 : G ^ (-(e * a)) = (G ^ (e * a))⁻¹ := Real.rpow_neg hG0.le _
  rw [Real.rpow_neg hP.le]
  rw [h3] at h1
  refine h1.trans ?_
  have hPa : 0 < P ^ a := Real.rpow_pos_of_pos hP a
  have hGa : 0 < G ^ (e * a) := Real.rpow_pos_of_pos hG0 _
  rw [inv_le_iff_one_le_mul₀ hGa]
  have h4 : 1 ≤ (C ^ (3 * a) * G ^ (e * a)) / P ^ a := by rw [one_le_div hPa]; exact h2
  calc (1 : ℝ) ≤ (C ^ (3 * a) * G ^ (e * a)) / P ^ a := h4
    _ = C ^ (3 * a) * (P ^ a)⁻¹ * G ^ (e * a) := by ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
