-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.gram_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:59.632251+00:00
-- url     : https://prove2.me/submissions/fe6b028d-f01c-4784-a4e1-93637f9eb992

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
theorem _root_.solution {ν ν' α α' : Type} [Fintype ν] [Fintype ν'] (e : ν' ≃ ν) (f : α' → α)
    (J : Matrix ν ν K) (Z : Matrix ν α K) :
    (Z.submatrix e f)ᴴ * J.submatrix e e * Z.submatrix e f = (Zᴴ * J * Z).submatrix f f := by
  rw [conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
end Formalism.FourierDecayAlt.P.S3x5
