-- Prove2me | solution 1 for Formalism.GM.Top.badCrit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:06.306732+00:00
-- url     : https://prove2.me/submissions/2b4d1be6-f815-440d-89b3-f569b8bbe546

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_BadCrit
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_MahlerMeasure_GamLead
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Definitions.Def_Formalism_MahlerMeasure_FinalT
import Theorems.Thm_Formalism_GM_bad_criterion_holds


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
theorem _root_.solution : M.BadCrit := bad_criterion_holds
end Formalism.GM.Top
