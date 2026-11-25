-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.int_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:58.755453+00:00
-- url     : https://prove2.me/submissions/e0068216-ccd5-4c97-9005-46d8ade71979

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
theorem _root_.solution {m n : Type} : Integral o (0 : Matrix m n k0) :=
  ⟨0, by ext; simp⟩
end Formalism.FourierDecayAlt.P.S3x8
