-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.gram_fromCols
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:20.149127+00:00
-- url     : https://prove2.me/submissions/d8a2a430-f9d7-4922-8ebf-1bb5c651c33f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (X : Matrix ν α K) (Y : Matrix ν β K) :
    (fromCols X Y)ᴴ * J * fromCols X Y =
      fromBlocks (Xᴴ * J * X) (Xᴴ * J * Y) (Yᴴ * J * X) (Yᴴ * J * Y) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols]
end Formalism.FourierDecayAlt.P.S3x5
