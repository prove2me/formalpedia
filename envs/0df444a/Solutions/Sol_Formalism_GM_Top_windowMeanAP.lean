-- Prove2me | solution 1 for Formalism.GM.Top.windowMeanAP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:52.12204+00:00
-- url     : https://prove2.me/submissions/9b6fe32f-e7b6-4f2c-9a5e-d5a63596d492

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Theorems.Thm_Formalism_GM_Top_windowCountAP
import Theorems.Thm_Formalism_GM_Top_discsDisjointAP
import Theorems.Thm_Formalism_GM_windowMeanAP_of


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
theorem _root_.solution : WindowMeanAP := windowMeanAP_of windowCountAP discsDisjointAP
end Formalism.GM.Top
