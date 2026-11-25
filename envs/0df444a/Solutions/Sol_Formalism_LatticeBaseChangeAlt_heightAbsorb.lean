-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.heightAbsorb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:15:23.902785+00:00
-- url     : https://prove2.me/submissions/d8585b25-5f32-456c-9e9c-68adcf91c6d3

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
theorem _root_.solution : HeightAbsorb := by
  intro HL Hde X Y a ha ha2 hY h1 h2
  have hm : X ≤ max X 0 := le_max_left _ _
  have hm0 : 0 ≤ max X 0 := le_max_right _ _
  nlinarith
end Formalism.LatticeBaseChangeAlt
