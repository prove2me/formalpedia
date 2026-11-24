-- Prove2me | solution 1 for Formalism.GM.Top.levelAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:11.344809+00:00
-- url     : https://prove2.me/submissions/cbfcc0c0-0cb9-416d-a80d-8884f999bcbc

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_LevelConst
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Theorems.Thm_Formalism_GM_alternatingChooseSum
import Theorems.Thm_Formalism_GM_levelAct_of


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
theorem _root_.solution : LevelAct := levelAct_of alternatingChooseSum
end Formalism.GM.Top
