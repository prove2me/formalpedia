-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x9.block32_levi_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:45.772196+00:00
-- url     : https://prove2.me/submissions/1e123b92-888b-4c85-bfbe-2ef230e54bd3

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
theorem _root_.solution {A : Type} [CommRing A] {r k : ℕ} (h : Matrix (Fin k) (Fin k) A) :
    b32 (hEmb r h) = 0 := by
  ext a b
  simp [b32, hEmb]
end Formalism.FourierDecayAlt.P.S3x9
