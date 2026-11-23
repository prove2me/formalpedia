-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.star_vecMul_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:50:00.883376+00:00
-- url     : https://prove2.me/submissions/1ef17ff5-e7ad-4f7a-a301-34020fabc6e3

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
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {α κ : Type} [Fintype α] (M : Matrix α κ K) (u : α → K)
    (h : Mᴴ *ᵥ u = 0) : star u ᵥ* M = 0 := by
  have h1 := Matrix.mulVec_conjTranspose M u
  rw [h] at h1
  have h2 := congrArg star h1
  simpa using h2.symm
end Formalism.FourierDecayAlt.P.S3x5
