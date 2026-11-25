-- Prove2me | solution 1 for Formalism.FG.addLawExample
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:09.229676+00:00
-- url     : https://prove2.me/submissions/e3e40829-3dd0-44c5-81a1-c4ba29b5d8b3

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
import Theorems.Thm_Formalism_FG_additive_law_example


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
theorem _root_.solution : AddLawExample := additive_law_example
end Formalism.FG
