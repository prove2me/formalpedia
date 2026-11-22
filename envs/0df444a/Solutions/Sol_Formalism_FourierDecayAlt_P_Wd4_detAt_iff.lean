-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.detAt_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:16:26.22413+00:00
-- url     : https://prove2.me/submissions/1afdd6ee-840b-430a-ad94-c30bc9fd8e34

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap

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
theorem _root_.solution (M : K → M2 B) (q : K → K) (Y : K) :
    DetAt M q Y ↔ (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y = q Y • YangianSpanCharacter.T.J B ∧
      M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • YangianSpanCharacter.T.J B := by
  simp only [DetAt, algebraMap_smul]
end Formalism.FourierDecayAlt.P.Wd4
