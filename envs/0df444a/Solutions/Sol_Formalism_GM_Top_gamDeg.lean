-- Prove2me | solution 1 for Formalism.GM.Top.gamDeg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:34.103161+00:00
-- url     : https://prove2.me/submissions/68765bda-ead4-41d8-8156-e4c487679e94

import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_GamLead
import Theorems.Thm_Formalism_GM_gamma_degree_bound


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
theorem _root_.solution : M.GamDeg := gamma_degree_bound
end Formalism.GM.Top
