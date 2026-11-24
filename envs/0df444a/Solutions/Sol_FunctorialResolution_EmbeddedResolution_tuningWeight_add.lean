-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:28.177795+00:00
-- url     : https://prove2.me/submissions/0ac4fab0-57cd-4589-8d04-5635f6ad9557

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_fun_add

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
    tuningWeight m (c + d) = tuningWeight m c + tuningWeight m d :=
  tuningWeight_fun_add m c d
end FunctorialResolution.EmbeddedResolution
