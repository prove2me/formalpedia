-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.block31_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:09.981738+00:00
-- url     : https://prove2.me/submissions/140e33d9-08ef-4b08-8d94-c4a08703c03d

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
    b31 (x * y) = b31 x * b11 y + b32 x * b21 y + b33 x * b31 y := by
  ext a b
  simp [b31, b11, b32, b21, b33, Matrix.mul_apply, Fintype.sum_sum_type, add_assoc]
end Formalism.FourierDecayAlt.P.S3x9
