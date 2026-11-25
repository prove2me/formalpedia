-- Prove2me | solution 1 for Formalism.FG.funEqHomV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:21.077466+00:00
-- url     : https://prove2.me/submissions/bf4883f1-5a0f-484d-ae29-8c63ded62e62

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
import Theorems.Thm_Formalism_FG_functional_equation_hom_vector


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
theorem _root_.solution : FunEqHomV.{u, v, w} := functional_equation_hom_vector
end Formalism.FG
