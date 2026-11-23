-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.weak_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:50:49.949273+00:00
-- url     : https://prove2.me/submissions/20a0e59b-ff3f-4f8a-85f5-5fca5978015d

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_pair_eq

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
theorem _root_.solution {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} {sig : ZMod d → ℝ}
    (hx : IsFlow l d D x) (h0 : ∀ s, 0 ≤ sig s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) :
    flowVal d x ≤ ∑ s, D s * sig s := by
  calc Formalism.IncomingBounds.flowVal d x = ∑ s, ∑ i ∈ oddLevels d, 1 * x s i := by simp [Formalism.IncomingBounds.flowVal]
    _ ≤ ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d))) * x s i :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (h1 s i hi) (hx.1 s i)
    _ = ∑ s, sig s * dpLoad l d x s := (pair_eq x sig).symm
    _ ≤ ∑ s, D s * sig s := Finset.sum_le_sum fun s _ => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hx.2 s) (h0 s)
end Formalism.IncomingBounds.FlowLoadBounds
