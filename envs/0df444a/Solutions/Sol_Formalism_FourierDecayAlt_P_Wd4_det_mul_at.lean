-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.det_mul_at
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:06.714806+00:00
-- url     : https://prove2.me/submissions/291d6780-e27d-439d-a427-eafc660d9b75

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_transpose_mul_of_comm


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
theorem _root_.solution (M N : K → M2 B) (q qN : K → K) (Y : K) (hM : DetAt M q Y) (hN : DetAt N qN Y)
    (hc : ∀ Y Y' i j k l, Commute (M Y i j) (N Y' k l)) :
    DetAt (fun Y => M Y * N Y) (fun Y => q Y * qN Y) Y := by
  rw [detAt_iff] at hM hN ⊢
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hN1, hN2⟩ := hN
  have ht : (M (Y + 1) * N (Y + 1))ᵀ = (N (Y + 1))ᵀ * (M (Y + 1))ᵀ :=
    transpose_mul_of_comm _ _ fun i j k l => (hc (Y + 1) (Y + 1) i j k l).eq
  refine ⟨?_, ?_⟩
  · show (M (Y + 1) * N (Y + 1))ᵀ * YangianSpanCharacter.T.J B * (M Y * N Y) = (q Y * qN Y) • YangianSpanCharacter.T.J B
    rw [ht]
    calc (N (Y + 1))ᵀ * (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * (M Y * N Y)
        = (N (Y + 1))ᵀ * ((M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y) * N Y := by simp only [mul_assoc]
      _ = (N (Y + 1))ᵀ * (q Y • YangianSpanCharacter.T.J B) * N Y := by rw [hM1]
      _ = q Y • ((N (Y + 1))ᵀ * YangianSpanCharacter.T.J B * N Y) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (q Y * qN Y) • YangianSpanCharacter.T.J B := by rw [hN1, smul_smul]
  · show M Y * N Y * YangianSpanCharacter.T.J B * (M (Y + 1) * N (Y + 1))ᵀ = (q Y * qN Y) • YangianSpanCharacter.T.J B
    rw [ht]
    calc M Y * N Y * YangianSpanCharacter.T.J B * ((N (Y + 1))ᵀ * (M (Y + 1))ᵀ)
        = M Y * (N Y * YangianSpanCharacter.T.J B * (N (Y + 1))ᵀ) * (M (Y + 1))ᵀ := by simp only [mul_assoc]
      _ = M Y * (qN Y • YangianSpanCharacter.T.J B) * (M (Y + 1))ᵀ := by rw [hN2]
      _ = qN Y • (M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (q Y * qN Y) • YangianSpanCharacter.T.J B := by rw [hM2, smul_smul, mul_comm]
end Formalism.FourierDecayAlt.P.Wd4
