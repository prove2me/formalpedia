-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.weight_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:12:04.767535+00:00
-- url     : https://prove2.me/submissions/c8ac2a95-79fe-4e87-8a8d-0bd8d33fac13

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThresholdExponentEstimate
import Theorems.Thm_Formalism_FourierDecayAlt_P_det_weyl_matrix


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.DetW := by
  intro s
  induction s with
  | zero => simp [G.wMat]
  | succ n ih =>
    rw [(det_weyl_matrix n).1, ih, ← pow_add]
    congr 1
    rcases n with _ | m
    · simp
    · have e : (m + 1 + 1) * (m + 1 + 1 - 1) = (m + 1) * (m + 1 - 1) + 2 * (m + 1) := by
        simp only [Nat.add_sub_cancel]; ring
      rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
      ring
end Formalism.FourierDecayAlt.P
