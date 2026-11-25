-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.independence_bound_of_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:09:13.853918+00:00
-- url     : https://prove2.me/submissions/e627baee-b7bd-4805-88ff-f396e060420c

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_independence_bound_of_span
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_independence_span_of_coefficient

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
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
variable {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : CoefficientIdentityCondition) : IndependenceBoundAllCharts :=
  independence_bound_of_span (independence_span_of_coefficient h)
end Formalism.L2.FormalSeriesBounds
