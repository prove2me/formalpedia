-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.isUnit_det_of_isUpUni
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:20.174421+00:00
-- url     : https://prove2.me/submissions/11886cdf-edb0-4449-9695-8d58c8167f38

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x3
open Matrix Formalism.FourierDecayAlt.S3
open Formalism.DoubleCosetMeasures (IsUpUni upUniG)
variable {A : Type} [CommRing A] {r k : ℕ}
namespace Formalism.FourierDecayAlt.P.S3x3
theorem _root_.solution {u : Matrix (Fin k) (Fin k) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [Formalism.DoubleCosetMeasures.isUpUni_det A hu]; exact isUnit_one
end Formalism.FourierDecayAlt.P.S3x3
