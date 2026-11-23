-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.gram_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:20.214594+00:00
-- url     : https://prove2.me/submissions/76decbd0-f573-483c-8093-a6a20da85d7c

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
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {ν α β : Type} [Fintype ν] (J : Matrix ν ν K) (Z : Matrix ν α K) (e : β → α) :
    (Z.submatrix id e)ᴴ * J * (Z.submatrix id e) = (Zᴴ * J * Z).submatrix e e := by
  ext i j
  rfl
end Formalism.FourierDecayAlt.P.S3x5
