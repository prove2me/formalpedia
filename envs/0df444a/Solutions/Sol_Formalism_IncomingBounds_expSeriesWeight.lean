-- Prove2me | solution 1 for Formalism.IncomingBounds.expSeriesWeight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:09.329601+00:00
-- url     : https://prove2.me/submissions/fea15e45-e6f4-48be-b4c0-47e95b727eba

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp
import Theorems.Thm_Formalism_IncomingBounds_expWeight_of
import Theorems.Thm_Formalism_IncomingBounds_thmPExp_valNat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : ExpWeight := expWeight_of thmPExp_valNat
end Formalism.IncomingBounds
