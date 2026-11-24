-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:35.734018+00:00
-- url     : https://prove2.me/submissions/5cfc9d61-8b24-42b3-96fc-2130cbe1caf8

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
theorem _root_.solution (m : ℕ) (c : ℕ → ℕ) :
    tuningWeight m c = ∑ j ∈ Finset.range m, (m - j) * c j := rfl
end FunctorialResolution.EmbeddedResolution
