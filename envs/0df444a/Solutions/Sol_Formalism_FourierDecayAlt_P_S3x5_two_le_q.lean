-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.two_le_q
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:57:12.912951+00:00
-- url     : https://prove2.me/submissions/482c414e-387e-4d06-b3c0-e4e05bacb3dc

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
open Matrix Polynomial Formalism.FourierDecayAlt.S3
variable {K : Type} [Field K] [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution {q : ℕ} (hc : Fintype.card K = q ^ 2) : 2 ≤ q := by
  have h := Fintype.one_lt_card (α := K)
  rw [hc] at h
  by_contra hq
  have : q = 0 ∨ q = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h
end Formalism.FourierDecayAlt.P.S3x5
