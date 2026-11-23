-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.pair_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:57.063597+00:00
-- url     : https://prove2.me/submissions/8cabe341-9fa8-436f-9070-b91431f38567

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
theorem _root_.solution (x : ZMod d → ℕ → ℝ) (a : ZMod d → ℝ) :
    ∑ s, a s * dpLoad l d x s =
      ∑ s, ∑ i ∈ oddLevels d, ((l : ℝ) ^ i * a s + a (s + (i : ZMod d))) * x s i := by
  have h2 : ∀ i : ℕ, ∑ s, a s * x (s - (i : ZMod d)) i = ∑ s, a (s + (i : ZMod d)) * x s i :=
    fun i => Fintype.sum_equiv (Equiv.subRight (i : ZMod d)) _ _ (fun s => by simp)
  simp only [dpLoad, mul_add, add_mul, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by ring
  · rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => h2 i
end Formalism.IncomingBounds.FlowLoadBounds
