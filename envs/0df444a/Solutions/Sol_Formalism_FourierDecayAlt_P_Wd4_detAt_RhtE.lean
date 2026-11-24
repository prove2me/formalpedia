-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.detAt_RhtE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:29.061799+00:00
-- url     : https://prove2.me/submissions/f082ee53-7c0a-4ae2-8c0b-9527307bd7d2

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_RhtE
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_detAt_iff

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
theorem _root_.solution (he : MU e) (Yb Y : K) (h1 : Yb - Y ≠ 1) (h2 : Yb - (Y + 1) ≠ 1) :
    DetAt (fun Y => RhtE e (Yb - Y)) (fun Y => (Yb - Y) / (Yb - Y - 1)) Y := by
  rw [detAt_iff]
  have hE : Yb - (Y + 1) = Yb - Y - 1 := by ring
  show (RhtE e (Yb - (Y + 1)))ᵀ * YangianSpanCharacter.T.J B * RhtE e (Yb - Y) =
      ((Yb - Y) / (Yb - Y - 1)) • YangianSpanCharacter.T.J B ∧
    RhtE e (Yb - Y) * YangianSpanCharacter.T.J B * (RhtE e (Yb - (Y + 1)))ᵀ = ((Yb - Y) / (Yb - Y - 1)) • YangianSpanCharacter.T.J B
  rw [hE] at h2 ⊢
  exact det_RhtE he (Yb - Y) h1 h2
end Formalism.FourierDecayAlt.P.Wd4
