-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr5.comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:37.063855+00:00
-- url     : https://prove2.me/submissions/1357aa0d-c349-4288-b806-60e6632a9ee0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QEFirstMulSecondEqSwap
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2OfFourEntries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr5
variable {B : Type} [Ring B] [StarRing B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Fr5
theorem _root_.solution {x xi g : B} (h1 : x * xi = 1) (h2 : xi * x = 1) (h : Commute x g) : Commute xi g := by
  show xi * g = g * xi
  calc xi * g = xi * g * (x * xi) := by rw [h1, mul_one]
    _ = xi * (x * g) * xi := by rw [h.eq]; simp only [mul_assoc]
    _ = g * xi := by rw [← mul_assoc xi x g, h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr5
