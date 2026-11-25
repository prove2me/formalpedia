-- Prove2me | solution 1 for Formalism.GM.Top.meanGam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:15:10.330407+00:00
-- url     : https://prove2.me/submissions/d974814a-e45b-47bc-99f1-912463470096

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_MahlerMeasure_GamLead
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Definitions.Def_Formalism_MahlerMeasure_FinalT
import Theorems.Thm_Formalism_GM_Top_gamDeg
import Theorems.Thm_Formalism_GM_Top_gamInt
import Theorems.Thm_Formalism_GM_Top_gamLead
import Theorems.Thm_Formalism_GM_Top_windowFullAP
import Theorems.Thm_Formalism_GM_meanGam_of


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
theorem _root_.solution : M.MeanGam := meanGam_of gamDeg gamLead gamInt windowFullAP
end Formalism.GM.Top
