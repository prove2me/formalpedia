-- Prove2me | solution 1 for Formalism.IncomingBounds.weakDuality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:17.055722+00:00
-- url     : https://prove2.me/submissions/4048277e-1b11-4137-9fcd-5292d88e4360

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_weak_core

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
theorem _root_.solution (l d : ℕ) [NeZero d] (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ)
    (sig : ZMod d → ℝ) (hx : IsFlow l d D x) (hsig : IsDual l d sig) :
    flowVal d x ≤ ∑ s, D s * sig s :=
  Formalism.IncomingBounds.FlowLoadBounds.weak_core hx (fun s => (hsig.1 s).1) hsig.2
end Formalism.IncomingBounds
