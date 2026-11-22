-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.coe_phi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:13.2572+00:00
-- url     : https://prove2.me/submissions/360ef36b-f8b5-4bbd-a9b9-5a1500ae199d

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x2
theorem _root_.solution (h : GL (Fin k) A) :
    (phi A r k h : Matrix (Idx r k) (Idx r k) A) = hEmb r (h : Matrix (Fin k) (Fin k) A) := rfl
end Formalism.FourierDecayAlt.P.S3x2
