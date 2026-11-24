-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.det_RhtE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:47.870903+00:00
-- url     : https://prove2.me/submissions/6f902aac-b67d-4882-9527-eccef0a88d7c

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_RhtE_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd4
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W
variable {K B : Type} [Field K] [Ring B] [Algebra K B]
variable {e : Fin 2 → Fin 2 → B}
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (he : MU e) (d : K) (h1 : d ≠ 1) (h2 : d - 1 ≠ 1) :
    (RhtE e (d - 1))ᵀ * YangianSpanCharacter.T.J B * RhtE e d = (d / (d - 1)) • YangianSpanCharacter.T.J B ∧
      RhtE e d * YangianSpanCharacter.T.J B * (RhtE e (d - 1))ᵀ = (d / (d - 1)) • YangianSpanCharacter.T.J B := by
  have h1' : d - 1 ≠ 0 := sub_ne_zero.2 h1
  have h2' : d - 1 - 1 ≠ 0 := sub_ne_zero.2 h2
  have hs : (d - 1 - 1)⁻¹ * (d - 1)⁻¹ * ((d - 1 + 1) * (d - 1 - 1)) = d / (d - 1) := by
    rw [sub_add_cancel]; field_simp
  have hs' : (d - 1)⁻¹ * (d - 1 - 1)⁻¹ * ((d - 1 + 1) * (d - 1 - 1)) = d / (d - 1) := by
    rw [sub_add_cancel]; field_simp
  have e1 := det1 he (d - 1)
  have e2 := det2 he (d - 1)
  rw [sub_add_cancel] at e1 e2
  rw [sub_add_cancel] at hs hs'
  rw [RhtE_transpose]
  unfold RhtE
  constructor
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, e2, smul_smul, smul_smul, hs]
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, e1, smul_smul, smul_smul, hs']
end Formalism.FourierDecayAlt.P.Wd4
