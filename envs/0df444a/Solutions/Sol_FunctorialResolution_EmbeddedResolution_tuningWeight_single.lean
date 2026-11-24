-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:30.526105+00:00
-- url     : https://prove2.me/submissions/a5875c6e-638a-407a-bb32-260c1400b0b3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_eq_sum

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
theorem _root_.solution (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningWeight m (Pi.single i 1) = m - i := by
  rw [tuningWeight_eq_sum, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni
end FunctorialResolution.EmbeddedResolution
