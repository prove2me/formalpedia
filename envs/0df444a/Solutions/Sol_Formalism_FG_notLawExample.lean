-- Prove2me | solution 1 for Formalism.FG.notLawExample
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:30:25.214798+00:00
-- url     : https://prove2.me/submissions/e08c4db2-274b-4ed0-830c-8db5f9f78d3e

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftAsm
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_HeightV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GaussV
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Theorems.Thm_Formalism_FG_not_a_law_example


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FG
universe u v w
namespace Formalism.FG
theorem _root_.solution : NotLawExample := not_a_law_example
end Formalism.FG
