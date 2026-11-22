-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.maxFlow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:33:08.701987+00:00
-- url     : https://prove2.me/submissions/93ba5010-8f9d-4b43-abd0-064458073dd6

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
theorem _root_.solution {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x)
    (hmax : ∀ y, IsFlow l d D y → flowVal d y ≤ flowVal d x) : maxFlow l d D = flowVal d x := by
  unfold Formalism.IncomingBounds.maxFlow
  refine IsGreatest.csSup_eq ⟨⟨x, hx, rfl⟩, ?_⟩
  rintro t ⟨y, hy, rfl⟩
  exact hmax y hy
end Formalism.IncomingBounds.FlowLoadBounds
