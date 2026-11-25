-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.independence_bound_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:09:39.536454+00:00
-- url     : https://prove2.me/submissions/ee3fe448-5511-499d-a964-f2ff3befba64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_independence_bound_of_span_raw

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
theorem _root_.solution (h : IndependenceSpanCondition) : IndependenceBoundAllCharts := by
  intro C _ _ V O _ _ dd Y d _ I _ p hrk H hR2 hAlt g a hbig N w x hg hV hind
  have := Y.algClosed
  obtain ⟨e, he⟩ := h C V O dd Y d I p hrk H hAlt g a hbig
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) e he N w x hg hV hind
end Formalism.L2.FormalSeriesBounds
