-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.localStepExt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:22.259124+00:00
-- url     : https://prove2.me/submissions/647bd474-2d11-4782-83ad-5b59fd06b378

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LevelsChain
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepExtOf
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepExt_of
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_quotientLengthExt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.LatticeBaseChangeAlt
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : LocalStepExt := localStepExt_of quotientLengthExt
end Formalism.LatticeBaseChangeAlt
