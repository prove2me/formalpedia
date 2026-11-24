-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.load_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:57.940673+00:00
-- url     : https://prove2.me/submissions/bd9afac3-ed04-4e88-8657-0981b0fc2d98

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
import Theorems.Thm_Formalism_IncomingBounds_FlowLoadBounds_sum_comb
import Theorems.Thm_P2M_Formalism_IncomingBounds_FlowLoadBounds_sum_comb__40021abff842

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
theorem _root_.solution (x y : ZMod d → ℕ → ℝ) (a b : ℝ) (s : ZMod d) :
    dpLoad l d (fun s i => a * x s i + b * y s i) s = a * dpLoad l d x s + b * dpLoad l d y s := by
  have e1 : ∑ i ∈ oddLevels d, (l : ℝ) ^ i * (a * x s i + b * y s i) =
      a * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i + b * ∑ i ∈ oddLevels d, (l : ℝ) ^ i * y s i :=
    sum_comb _ _ _ _ _ _
  have e2 : ∑ i ∈ oddLevels d, (a * x (s - (i : ZMod d)) i + b * y (s - (i : ZMod d)) i) =
      a * ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i + b * ∑ i ∈ oddLevels d, y (s - (i : ZMod d)) i :=
    sum_comb' _ _ _ _ _
  simp only [dpLoad]
  rw [e1, e2]
  ring
end Formalism.IncomingBounds.FlowLoadBounds
