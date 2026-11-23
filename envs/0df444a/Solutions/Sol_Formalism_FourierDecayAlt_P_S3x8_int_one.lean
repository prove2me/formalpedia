-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:19:57.693296+00:00
-- url     : https://prove2.me/submissions/61dec2c3-7400-4f5e-9f0c-62b5579c92db

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
variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution {m : Type} [DecidableEq m] : Integral o (1 : Matrix m m k0) :=
  ⟨1, by simp⟩
end Formalism.FourierDecayAlt.P.S3x8
