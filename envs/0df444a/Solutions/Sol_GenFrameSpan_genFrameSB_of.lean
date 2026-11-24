-- Prove2me | solution 1 for GenFrameSpan.genFrameSB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:17.043456+00:00
-- url     : https://prove2.me/submissions/130ccbf5-c621-4c59-a756-35daf722c5c8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_GenFrameSBOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GenFrameSpan
open CutKW
namespace GenFrameSpan
theorem _root_.solution (hb : StepBack) (hs : StepSpan) (ht : StepSat) : CutKW.KWsb := by
  intro hSB Lt _ _ l _ N0 N1 nu Th B
  exact ⟨fun h I => ht hSB Lt l N0 nu _ B (hs Lt l N0 N1 nu Th I) (h I), hb Lt l N0 N1 nu Th B⟩
end GenFrameSpan
