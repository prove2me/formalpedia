-- Prove2me | solution 1 for GenFrameSpan.genFrameSB_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:14:08.261912+00:00
-- url     : https://prove2.me/submissions/ce854195-3f3d-403d-9bfd-b9090147566b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_StepBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOfSpan
import Theorems.Thm_GenFrameSpan_stepSat
import Theorems.Thm_GenFrameSpan_genFrameSB_of
import Theorems.Thm_GenFrameSpan_stepBack


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GenFrameSpan
namespace GenFrameSpan
theorem _root_.solution (hs : StepSpan) : CutKW.KWsb := genFrameSB_of stepBack hs stepSat
end GenFrameSpan
