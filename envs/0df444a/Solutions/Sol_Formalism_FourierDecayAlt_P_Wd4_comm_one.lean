-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.comm_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:51.25152+00:00
-- url     : https://prove2.me/submissions/fa925d9a-ed1e-4a02-94e3-8529cda8fbc5

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
theorem _root_.solution (b : B) (i j : Fin 2) : Commute ((1 : M2 B) i j) b := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Commute.one_left _
  · exact Commute.zero_left _
end Formalism.FourierDecayAlt.P.Wd4
