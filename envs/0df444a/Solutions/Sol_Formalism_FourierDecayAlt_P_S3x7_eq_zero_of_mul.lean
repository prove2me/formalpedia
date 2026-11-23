-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.eq_zero_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:14:57.285543+00:00
-- url     : https://prove2.me/submissions/283a9a4d-f182-4094-9150-908f08296baa

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y : Matrix n m A} (h : f * Y = 0) : Y = 0 := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.mul_zero]
end Formalism.FourierDecayAlt.P.S3x7
