-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.eval_two_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:30.33726+00:00
-- url     : https://prove2.me/submissions/24ddaed1-cda0-4d08-a66b-4ca8f195e72d

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
namespace Formalism.FourierDecayAlt.P.Wd4
theorem _root_.solution (c : K) (M : M2 B) : E2 (c • M) = c • E2 M := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E2, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd4
