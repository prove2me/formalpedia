-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.lcancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:11:46.989127+00:00
-- url     : https://prove2.me/submissions/137122f0-a7ac-4c86-9239-e8ae97731de3

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
theorem _root_.solution {n m : Type} [Fintype n] [DecidableEq n] {f : Matrix n n A} (hf : IsUnit f.det)
    {Y Z : Matrix n m A} (h : f * Y = f * Z) : Y = Z := by
  rw [← Matrix.nonsing_inv_mul_cancel_left f Y hf, h, Matrix.nonsing_inv_mul_cancel_left f Z hf]
end Formalism.FourierDecayAlt.P.S3x8
