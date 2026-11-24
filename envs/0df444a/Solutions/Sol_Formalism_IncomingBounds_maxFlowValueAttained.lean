-- Prove2me | solution 1 for Formalism.IncomingBounds.maxFlowValueAttained
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:51.766953+00:00
-- url     : https://prove2.me/submissions/5889d6da-5479-4d00-a9c1-a69481f0b109

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_exists_opt_flow
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_maxFlow_eq

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
open Set
open scoped Pointwise
open Formalism Formalism.IncomingBounds
open FlowLoadBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : FlowAttained := by
  intro l d _ hl hd hev D hD
  obtain ⟨x, hx, hmax⟩ := Formalism.IncomingBounds.FlowLoadBounds.exists_opt_flow (by omega : 1 ≤ l) D hD
  exact ⟨x, hx, (Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq hx hmax).symm⟩
end Formalism.IncomingBounds
