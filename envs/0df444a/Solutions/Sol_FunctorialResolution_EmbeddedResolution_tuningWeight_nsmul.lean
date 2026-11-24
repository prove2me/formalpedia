-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:23.055225+00:00
-- url     : https://prove2.me/submissions/55afab88-52da-4132-ab80-096343b18b48

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_mul_left

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
    tuningWeight m (n • c) = n * tuningWeight m c := by
  have : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [this, tuningWeight_mul_left]
end FunctorialResolution.EmbeddedResolution
