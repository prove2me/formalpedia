-- Prove2me | solution 1 for Formalism.GM.Top.windowCountAP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:57.613024+00:00
-- url     : https://prove2.me/submissions/43745a2f-bf1c-4350-a4e9-120cf7fe4d1b

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Theorems.Thm_Formalism_GM_window_count_progression


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
theorem _root_.solution : WindowCountAP := window_count_progression
end Formalism.GM.Top
