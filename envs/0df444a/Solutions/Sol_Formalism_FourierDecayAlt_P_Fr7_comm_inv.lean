-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:37.135341+00:00
-- url     : https://prove2.me/submissions/0e295e5e-bd71-48ec-941b-3534f87a420c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution {B : Type} [Monoid B] {x xi b : B} (h1 : x * xi = 1) (h2 : xi * x = 1)
    (h : Commute x b) : Commute xi b := by
  show xi * b = b * xi
  calc xi * b = xi * b * (x * xi) := by rw [h1, mul_one]
    _ = xi * (x * b) * xi := by rw [h.eq]; simp only [mul_assoc]
    _ = b * xi := by rw [← mul_assoc, h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr7
