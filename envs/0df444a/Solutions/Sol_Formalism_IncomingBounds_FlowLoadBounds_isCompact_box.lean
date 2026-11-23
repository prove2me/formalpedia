-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:56.83603+00:00
-- url     : https://prove2.me/submissions/ab4797a9-bc48-48f3-9657-b7ac31fa1881

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
theorem _root_.solution (R : ℝ) : IsCompact (box d R) := by
  unfold box
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
end Formalism.IncomingBounds.FlowLoadBounds
