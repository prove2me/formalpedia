-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.independence_bound_self_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:11:11.408378+00:00
-- url     : https://prove2.me/submissions/9e8ab239-9f23-43ec-8999-3a9ee316d078

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
theorem _root_.solution (h : CoefficientIdentitySelfConjugate) : IndependenceBoundSelfConjugate := by
  unfold IndependenceBoundSelfConjugate AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.rawSelf p) hrk H hR2 (h C V O dd Y d I0 p hrk H)
end Formalism.L2.FormalSeriesBounds
