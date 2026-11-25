-- Prove2me | solution 1 for Formalism.GM.weight_space_dimension_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:15:02.369952+00:00
-- url     : https://prove2.me/submissions/c16a0552-c168-4fae-84f8-99bbd942f577

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_highest_weight_dim_monotone

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
namespace Formalism.GM
theorem _root_.solution : M.WeightSpaceDimMonotone := DimensionMonotonicity.highest_weight_dim_monotone
end Formalism.GM
