-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.independence_bound_all_charts_of_coefficient_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:09:09.244873+00:00
-- url     : https://prove2.me/submissions/0122c8a9-bb2b-41b7-9cde-4766c4c33797

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoefficientIdentitySelfConjugate
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_IndependenceBoundPlain_independence_bound_raw

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
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (h : CoefficientIdentityCondition) : IndependenceBoundAllCharts := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.raw p) hrk H hR2 (h C V O dd Y d I p hrk H)
end Formalism.L2.FormalSeriesBounds
