-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.trunc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:58.146348+00:00
-- url     : https://prove2.me/submissions/cec85bd9-d747-4c25-8b62-835f1e948943

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained

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
open Formalism.IncomingBounds.FlowLoadBounds
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowLoadBounds
theorem _root_.solution {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) : ∀ s i, 0 ≤ trunc d x s i := by
  intro s i
  simp only [trunc]
  split_ifs
  · exact hx s i
  · exact le_rfl
end Formalism.IncomingBounds.FlowLoadBounds
