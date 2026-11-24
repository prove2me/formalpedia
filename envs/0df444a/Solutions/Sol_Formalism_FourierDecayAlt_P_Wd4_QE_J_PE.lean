-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.QE_J_PE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:56.301105+00:00
-- url     : https://prove2.me/submissions/b2c28a90-a620-489b-a6ce-7b326f9bb26e

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
theorem _root_.solution (he : MU e) : QE e * YangianSpanCharacter.T.J B * PE e = -(QE e * YangianSpanCharacter.T.J B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [YangianSpanCharacter.T.J, PE, QE, Matrix.mul_apply, Fin.sum_univ_two, he.mul]
end Formalism.FourierDecayAlt.P.Wd4
