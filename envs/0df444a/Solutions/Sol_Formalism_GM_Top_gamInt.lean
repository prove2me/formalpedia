-- Prove2me | solution 1 for Formalism.GM.Top.gamInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:14:59.630458+00:00
-- url     : https://prove2.me/submissions/8422f906-f587-4254-98f6-091a1b9a0c00

import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_GamLead
import Theorems.Thm_Formalism_GM_gamma_integrality


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.Top
open Formalism.GM
namespace Formalism.GM.Top
theorem _root_.solution : M.GamInt := gamma_integrality
end Formalism.GM.Top
