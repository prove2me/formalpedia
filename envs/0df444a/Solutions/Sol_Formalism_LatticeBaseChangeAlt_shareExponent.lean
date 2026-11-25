-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.shareExponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:42.751637+00:00
-- url     : https://prove2.me/submissions/8281c83c-3cd2-4fef-9e25-3b6445ce7d1a

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FilIntegerStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : ShareExponent := by
  intro D T δ xL xF hδ h1 h2
  have hD : (0 : ℝ) ≤ D := by positivity
  nlinarith
end Formalism.LatticeBaseChangeAlt
