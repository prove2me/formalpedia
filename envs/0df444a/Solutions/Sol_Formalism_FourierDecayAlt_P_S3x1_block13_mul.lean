-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.block13_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:45.049912+00:00
-- url     : https://prove2.me/submissions/9e693576-73e6-4bd5-93d4-57da95f9ebe8

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x1
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x1
theorem _root_.solution (x y : Matrix (Idx r k) (Idx r k) A) :
    b13 (x * y) = b11 x * b13 y + b12 x * b23 y + b13 x * b33 y := by
  ext a b
  simp [b13, b11, b12, b13, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
end Formalism.FourierDecayAlt.P.S3x1
