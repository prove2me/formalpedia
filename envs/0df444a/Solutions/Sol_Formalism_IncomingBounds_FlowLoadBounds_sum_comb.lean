-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.sum_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:09.332807+00:00
-- url     : https://prove2.me/submissions/b2238fc4-1e67-4459-948b-0ceb829a26ad

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
theorem _root_.solution {ι : Type*} (S : Finset ι) (f g c : ι → ℝ) (a b : ℝ) :
    ∑ i ∈ S, c i * (a * f i + b * g i) = a * ∑ i ∈ S, c i * f i + b * ∑ i ∈ S, c i * g i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
end Formalism.IncomingBounds.FlowLoadBounds
