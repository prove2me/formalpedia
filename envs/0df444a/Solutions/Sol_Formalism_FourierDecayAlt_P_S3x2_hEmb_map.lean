-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x2.hEmb_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:53.776255+00:00
-- url     : https://prove2.me/submissions/a847988a-e6f5-471a-ad12-8b3c4a74aeb2

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
theorem _root_.solution {B : Type} [CommRing B] (f : A →+* B) (h : Matrix (Fin k) (Fin k) A) :
    (hEmb r h).map f = hEmb r (h.map f) := by
  simp [hEmb, midEmb, Matrix.fromBlocks_map]
end Formalism.FourierDecayAlt.P.S3x2
