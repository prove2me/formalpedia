-- Prove2me | solution 1 for Formalism.GM.Top.discsDisjointAP
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:11.221977+00:00
-- url     : https://prove2.me/submissions/edc23c9c-dcac-40af-951e-c1b86ca17f17

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowMeanAP
import Definitions.Def_Formalism_MahlerMeasure_FinalD
import Definitions.Def_Formalism_MahlerMeasure_CoarseLevelSlackInequalities
import Theorems.Thm_Formalism_GM_root_discs_disjoint_progression


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
theorem _root_.solution : DiscsDisjointAP := root_discs_disjoint_progression
end Formalism.GM.Top
