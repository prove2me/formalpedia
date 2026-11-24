-- Prove2me | solution 1 for Formalism.GM.Top.windowFullAP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:18.440039+00:00
-- url     : https://prove2.me/submissions/bb11ae79-8e9f-431f-a98a-eea384c0b004

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Theorems.Thm_Formalism_GM_Top_windowMeanAP
import Theorems.Thm_Formalism_GM_Top_valuation_window_lower_bound
import Theorems.Thm_Formalism_GM_windowFullAP_of


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
theorem _root_.solution : WindowFullAP := windowFullAP_of valuation_window_lower_bound windowMeanAP
end Formalism.GM.Top
