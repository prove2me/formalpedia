-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.hEmb_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.407879+00:00
-- url     : https://prove2.me/submissions/bb3f5f40-6dfb-401a-8bab-4622d6378334

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
theorem _root_.solution (h : Matrix (Fin k) (Fin k) A) (a b : Fin k) :
    hEmb r h (Sum.inr (Sum.inl (Sum.inl a))) (Sum.inr (Sum.inl (Sum.inl b))) = h a b := rfl
end Formalism.FourierDecayAlt.P.S3x2
