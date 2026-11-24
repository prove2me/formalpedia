-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.det_RhE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:47.331651+00:00
-- url     : https://prove2.me/submissions/7d915fb5-0f8a-4f96-a251-6aed1b5a4157

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det1
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_RhE_transpose

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
theorem _root_.solution (he : MU e) (D : K) (h0 : D ≠ 0) (h1 : D ≠ 1) :
    (RhE e (D + 1))ᵀ * YangianSpanCharacter.T.J B * RhE e D = ((D + 1) / D) • YangianSpanCharacter.T.J B ∧
      RhE e D * YangianSpanCharacter.T.J B * (RhE e (D + 1))ᵀ = ((D + 1) / D) • YangianSpanCharacter.T.J B := by
  have h1' : D - 1 ≠ 0 := sub_ne_zero.2 h1
  have hs : (D + 1 - 1)⁻¹ * (D - 1)⁻¹ * ((D + 1) * (D - 1)) = (D + 1) / D := by
    rw [add_sub_cancel_right]; field_simp
  have hs' : (D - 1)⁻¹ * (D + 1 - 1)⁻¹ * ((D + 1) * (D - 1)) = (D + 1) / D := by
    rw [add_sub_cancel_right]; field_simp
  rw [RhE_transpose]
  unfold RhE
  constructor
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, det1 he D, smul_smul, smul_smul, hs]
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, det2 he D, smul_smul, smul_smul, hs']
end Formalism.FourierDecayAlt.P.Wd4
