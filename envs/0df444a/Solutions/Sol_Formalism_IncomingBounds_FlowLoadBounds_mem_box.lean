-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.mem_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:23.115608+00:00
-- url     : https://prove2.me/submissions/c97df827-9454-449c-a797-d27eb40b1906

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
theorem _root_.solution {R : ℝ} {x : ZMod d → ℕ → ℝ} : x ∈ box d R ↔ ∀ s i, 0 ≤ x s i ∧ x s i ≤ R := by
  simp only [box, Set.mem_univ_pi, Set.mem_Icc]
end Formalism.IncomingBounds.FlowLoadBounds
