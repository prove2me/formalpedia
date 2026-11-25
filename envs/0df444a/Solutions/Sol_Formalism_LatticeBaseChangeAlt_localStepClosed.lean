-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localStepClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:17:51.926357+00:00
-- url     : https://prove2.me/submissions/e6a28cc0-87b3-4ab6-9081-272d3f6ff5ea

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosedOf
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LeadingTermLength
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_leadingTermLength
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepClosed_of


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
theorem _root_.solution : LocalStepClosed := localStepClosed_of leadingTermLength
end Formalism.LatticeBaseChangeAlt
