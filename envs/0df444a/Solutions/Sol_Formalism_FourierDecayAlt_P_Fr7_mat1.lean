-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.mat1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:45.325374+00:00
-- url     : https://prove2.me/submissions/e99b2a1b-e445-4d76-aaae-2645d60c3895

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
theorem _root_.solution {B : Type} [Ring B] (z zi w wi G Gi l : B) (hz : zi * z = 1) (hw : wi * w = 1)
    (hG : G * Gi = 1) :
    (!![zi, 0; 0, wi] * !![1, 0; G * l, G]) * (!![1, 0; -l, Gi] * !![z, 0; 0, w]) = 1 := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  · exact hz
  · noncomm_ring
  · rw [← mul_assoc, mul_assoc wi G Gi, hG, mul_one, hw]
end Formalism.FourierDecayAlt.P.Fr7
