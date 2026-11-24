-- Prove2me | solution 1 for GenFrameSpan.stepSat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:30.236601+00:00
-- url     : https://prove2.me/submissions/2d09bf55-a6e7-4898-94d3-22023219693a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_StepBack
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOfSpan
import Theorems.Thm_GenFrameSpan_projZ
import Theorems.Thm_GenFrameSpan_stepSat_of


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
theorem _root_.solution : StepSat := stepSat_of projZ
end GenFrameSpan
