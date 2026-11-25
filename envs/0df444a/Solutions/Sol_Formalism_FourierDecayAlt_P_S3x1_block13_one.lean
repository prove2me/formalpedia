-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x1.block13_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:35:48.535558+00:00
-- url     : https://prove2.me/submissions/a466931d-c39a-44f9-bc9e-b9981466ccbf

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
theorem _root_.solution : b13 (1 : Matrix (Idx r k) (Idx r k) A) = 0 := by
  ext a b
  simp [b13, Matrix.one_apply]
end Formalism.FourierDecayAlt.P.S3x1
