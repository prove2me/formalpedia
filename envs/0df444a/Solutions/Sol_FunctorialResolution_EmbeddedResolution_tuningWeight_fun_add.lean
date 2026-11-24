-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_fun_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:00.666584+00:00
-- url     : https://prove2.me/submissions/ad337c53-09dd-4170-901d-fc9550a461d6

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
theorem _root_.solution (m : ℕ) (c d : ℕ → ℕ) :
    tuningWeight m (fun j => c j + d j) = tuningWeight m c + tuningWeight m d := by
  simp [tuningWeight, Nat.mul_add, Finset.sum_add_distrib]
end FunctorialResolution.EmbeddedResolution
