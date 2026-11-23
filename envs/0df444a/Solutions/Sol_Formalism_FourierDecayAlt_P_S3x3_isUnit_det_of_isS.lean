-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x3.isUnit_det_of_isS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:21.578339+00:00
-- url     : https://prove2.me/submissions/c66bc694-37bb-4505-9623-42ed01b0c28f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemIntegralGlOfMiddleBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_hEmb
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x3_det_of_isN

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
theorem _root_.solution {x : Matrix (Idx r k) (Idx r k) A} (hx : IsS x) : IsUnit x.det := by
  obtain ⟨n, h', hn, ⟨h, hh, rfl⟩, rfl⟩ := hx
  rw [Matrix.det_mul, det_of_isN hn, det_hEmb, one_mul]
  exact hh
end Formalism.FourierDecayAlt.P.S3x3
