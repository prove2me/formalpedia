-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.block23_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:07.727923+00:00
-- url     : https://prove2.me/submissions/23965437-26e4-4177-b4e3-53d0289902e6

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} {r k : ℕ}
variable [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution (x y : Matrix (Idx r k) (Idx r k) A) :
    b23 (x * y) = b21 x * b13 y + b22 x * b23 y + b23 x * b33 y := by
  ext a b
  simp [b21, b22, b23, b13, b23, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
end Formalism.FourierDecayAlt.P.S3x8
