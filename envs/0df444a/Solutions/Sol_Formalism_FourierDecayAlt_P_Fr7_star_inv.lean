-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.star_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.71892+00:00
-- url     : https://prove2.me/submissions/d90e19f2-af42-402b-96f5-4e90ea76adb0

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
theorem _root_.solution {B : Type} [Monoid B] [StarMul B] {x xi : B} (h1 : x * xi = 1)
    (h : star x = x) : star xi = xi := by
  have h2 : star xi * x = 1 := by
    have := congrArg star h1
    rwa [star_mul, h, star_one] at this
  calc star xi = star xi * (x * xi) := by rw [h1, mul_one]
    _ = (star xi * x) * xi := (mul_assoc _ _ _).symm
    _ = xi := by rw [h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr7
