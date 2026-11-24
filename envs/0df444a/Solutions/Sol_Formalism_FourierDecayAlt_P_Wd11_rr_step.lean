-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.rr_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:51:09.572809+00:00
-- url     : https://prove2.me/submissions/ce4c2dd7-ad13-421a-b3e0-a93a06b02221

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution {B : Type*} [Ring B] [StarRing B] {V Vi RR TA W L R : B}
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR) (hWV : Commute W V)
    (hsRR : Commute (star W) RR) (hsV : Commute (star W) V)
    (hT : Vi * TA * V = L * TA * R) (hL : star W * L = 1) (hR : R * W = 1) :
    star (W * V) * (RR * TA) * (W * V) = RR * TA := by
  have k : TA * V = V * (L * TA * R) := by
    rw [← hT]; simp only [← mul_assoc]; rw [h1, one_mul]
  calc star (W * V) * (RR * TA) * (W * V)
      = star V * (star W * RR) * (TA * V) * W := by
        rw [star_mul, hWV.eq]; simp only [mul_assoc]
    _ = star V * (RR * star W) * (V * (L * TA * R)) * W := by rw [hsRR.eq, k]
    _ = star V * RR * (star W * V) * (L * TA * R) * W := by simp only [mul_assoc]
    _ = star V * RR * (V * star W) * (L * TA * R) * W := by rw [hsV.eq]
    _ = (star V * RR * V) * (star W * L) * TA * (R * W) := by simp only [mul_assoc]
    _ = RR * TA := by rw [h3, hL, hR, mul_one, mul_one]
end Formalism.FourierDecayAlt.P.Wd11
