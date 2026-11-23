-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.block32_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:48.963798+00:00
-- url     : https://prove2.me/submissions/9a36906f-4c52-4bf5-bbfc-01d447f2fc26

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Minors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block32EqZeroOfUnipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x9
open Matrix Finset
open Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
namespace Formalism.FourierDecayAlt.P.S3x9
theorem _root_.solution {A : Type} [CommRing A] {r k : ℕ} (x y : Matrix (Idx r k) (Idx r k) A) :
    b32 (x * y) = b31 x * b12 y + b32 x * b22 y + b33 x * b32 y := by
  ext a b
  simp [b31, b12, b32, b22, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
end Formalism.FourierDecayAlt.P.S3x9
