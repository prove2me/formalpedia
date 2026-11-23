-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.firstEmbed_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:52.05479+00:00
-- url     : https://prove2.me/submissions/b1d5a660-9ca7-4dba-af60-c840afb6244a

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
theorem _root_.solution (M N : M2 B) : E1 (M - N) = E1 M - E1 N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E1, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd4
