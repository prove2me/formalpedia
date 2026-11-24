-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.trunc_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:30.909653+00:00
-- url     : https://prove2.me/submissions/f4e84614-dcd9-4e3c-a4b8-38c6aa8283df

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_coord_le_load

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
theorem _root_.solution (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ s, dpLoad l d x s ≤ R) : ∀ s i, trunc d x s i ≤ R := by
  intro s i
  simp only [trunc]
  split_ifs with hi
  · exact (coord_le_load hl hx s hi).trans (h s)
  · exact hR
end Formalism.IncomingBounds.FlowLoadBounds
