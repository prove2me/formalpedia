-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.eta_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:57.35616+00:00
-- url     : https://prove2.me/submissions/db46e4e9-4699-4014-aea6-068b8e11d839

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
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (i : ℤ) : ((η : ℝ) ^ i = 1 ∨ (η : ℝ) ^ i = -1) := by
  rcases hη with rfl | rfl
  · left; simp
  · rcases Int.even_or_odd i with h | h
    · left; push_cast; exact h.neg_one_zpow
    · right; push_cast; exact h.neg_one_zpow
end Formalism.FourierDecayAlt.P.S3x5
