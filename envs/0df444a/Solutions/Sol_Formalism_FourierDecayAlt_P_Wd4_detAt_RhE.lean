-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.detAt_RhE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:28.951911+00:00
-- url     : https://prove2.me/submissions/50b450e6-6939-407f-933b-651f3d79f0da

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd4_det_RhE
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
theorem _root_.solution (he : MU e) (Ya Y : K) (h1 : Y - Ya ≠ 1) (h2 : Y + 1 - Ya ≠ 1) :
    DetAt (fun Y => RhE e (Y - Ya)) (fun Y => (Y - Ya + 1) / (Y - Ya)) Y := by
  rw [detAt_iff]
  have h0 : Y - Ya ≠ 0 := by
    intro h; apply h2; rw [add_sub_right_comm, h, zero_add]
  have hE : Y + 1 - Ya = Y - Ya + 1 := by ring
  show (RhE e (Y + 1 - Ya))ᵀ * YangianSpanCharacter.T.J B * RhE e (Y - Ya) = ((Y - Ya + 1) / (Y - Ya)) • YangianSpanCharacter.T.J B ∧
    RhE e (Y - Ya) * YangianSpanCharacter.T.J B * (RhE e (Y + 1 - Ya))ᵀ = ((Y - Ya + 1) / (Y - Ya)) • YangianSpanCharacter.T.J B
  rw [hE]
  exact det_RhE he (Y - Ya) h0 h1
end Formalism.FourierDecayAlt.P.Wd4
