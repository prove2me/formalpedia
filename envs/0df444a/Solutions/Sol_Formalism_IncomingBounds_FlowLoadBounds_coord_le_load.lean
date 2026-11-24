-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.coord_le_load
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:07.855723+00:00
-- url     : https://prove2.me/submissions/cbb16908-46e6-4462-a210-0651c3318f84

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
theorem _root_.solution (hl : 1 ≤ l) {x : ZMod d → ℕ → ℝ} (hx : ∀ s i, 0 ≤ x s i) (s : ZMod d)
    {i : ℕ} (hi : i ∈ oddLevels d) : x s i ≤ dpLoad l d x s := by
  have hl' : (1 : ℝ) ≤ (l : ℝ) ^ i := by
    have h : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact one_le_pow₀ h
  have h1 : x s i ≤ (l : ℝ) ^ i * x s i := le_mul_of_one_le_left (hx s i) hl'
  have h2 : (l : ℝ) ^ i * x s i ≤ ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x s j :=
    Finset.single_le_sum (f := fun j => (l : ℝ) ^ j * x s j)
      (fun j _ => mul_nonneg (by positivity) (hx s j)) hi
  have h3 : 0 ≤ ∑ j ∈ oddLevels d, x (s - (j : ZMod d)) j := Finset.sum_nonneg fun j _ => hx _ _
  unfold dpLoad
  linarith
end Formalism.IncomingBounds.FlowLoadBounds
