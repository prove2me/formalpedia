-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.swap_mul_secondEmbed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:58.911877+00:00
-- url     : https://prove2.me/submissions/ca7fb71e-4cfc-421d-b0cb-c19450e0f11c

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
theorem _root_.solution (M : M2 B) : Pf B * E2 M = E1 M * Pf B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, Matrix.mul_apply, Fintype.sum_prod_type]
end Formalism.FourierDecayAlt.P.Wd4
