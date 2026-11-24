-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:29.195831+00:00
-- url     : https://prove2.me/submissions/5b210a38-f73c-4c22-8263-7350768ea75a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (m n : ℕ) (c : ℕ → ℕ) :
    tuningWeight m (fun j => n * c j) = n * tuningWeight m c := by
  simp [tuningWeight, Finset.mul_sum, Nat.mul_left_comm]
end FunctorialResolution.EmbeddedResolution
