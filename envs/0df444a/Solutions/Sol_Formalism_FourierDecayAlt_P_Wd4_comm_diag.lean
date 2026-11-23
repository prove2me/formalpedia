-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd4.comm_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:51.148241+00:00
-- url     : https://prove2.me/submissions/d3a03339-d756-4661-a07f-e5e13f13f724

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
theorem _root_.solution (X : M2 B) (b : B) (h : ∀ i j, Commute (X i j) b) :
    X * Matrix.diagonal (fun _ => b) = Matrix.diagonal (fun _ => b) * X := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (h i j).eq
end Formalism.FourierDecayAlt.P.Wd4
