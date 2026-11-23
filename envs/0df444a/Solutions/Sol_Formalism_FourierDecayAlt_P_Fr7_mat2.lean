-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.mat2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:27.781805+00:00
-- url     : https://prove2.me/submissions/75c7f45b-1ba9-45f6-84a8-47672659c8f2

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
theorem _root_.solution {B : Type} [Ring B] (z zi w wi G Gi l : B) (hz : z * zi = 1) (hw : w * wi = 1)
    (hG : Gi * G = 1) :
    (!![1, 0; -l, Gi] * !![z, 0; 0, w]) * (!![zi, 0; 0, wi] * !![1, 0; G * l, G]) = 1 := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, zero_mul, add_zero, zero_add, one_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp
  · exact hz
  · rw [mul_assoc l, hz, mul_one, mul_assoc Gi, ← mul_assoc w, hw, one_mul, ← mul_assoc, hG,
      one_mul, neg_add_cancel]
  · rw [mul_assoc Gi, ← mul_assoc w, hw, one_mul, hG]
end Formalism.FourierDecayAlt.P.Fr7
