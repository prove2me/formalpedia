-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.mul_mul_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.416689+00:00
-- url     : https://prove2.me/submissions/b6f6fcd7-9d22-4f0c-ba55-e0c857294977

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
theorem _root_.solution {B : Type} [Monoid B] {c ci d di : B} (h1 : c * ci = 1) (h2 : d * di = 1)
    (h : Commute d ci) : c * d * (ci * di) = 1 := by
  calc c * d * (ci * di) = c * (d * ci) * di := by simp only [mul_assoc]
    _ = c * (ci * d) * di := by rw [h.eq]
    _ = (c * ci) * (d * di) := by simp only [mul_assoc]
    _ = 1 := by rw [h1, h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr7
