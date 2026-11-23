-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr10.star_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:07.29483+00:00
-- url     : https://prove2.me/submissions/a0760d03-1fee-4c95-9b56-1978ea18c3fb

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr10
open Formalism.FourierDecayAlt.P.Wd1
variable {B : Type} [Ring B]
namespace Formalism.FourierDecayAlt.P.Fr10
theorem _root_.solution [StarRing B] {x xi : B} (h1 : x * xi = 1) (h : star x = x) : star xi = xi := by
  have h3 : star xi * x = 1 := by
    have := congrArg star h1
    rwa [star_mul, star_one, h] at this
  calc star xi = star xi * (x * xi) := by rw [h1, mul_one]
    _ = (star xi * x) * xi := by rw [mul_assoc]
    _ = xi := by rw [h3, one_mul]
end Formalism.FourierDecayAlt.P.Fr10
