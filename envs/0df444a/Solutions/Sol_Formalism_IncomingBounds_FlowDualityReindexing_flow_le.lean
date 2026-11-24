-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.flow_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:06.685206+00:00
-- url     : https://prove2.me/submissions/a6f2e917-1f70-49eb-8b61-141cc84c5ccd

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd

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
open Formalism Formalism.IncomingBounds
open Formalism.IncomingBounds.FlowDualityReindexing
variable {l d : ℕ} [NeZero d]
namespace Formalism.IncomingBounds.FlowDualityReindexing
theorem _root_.solution (D : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x) (t : ZMod d)
    (i : ℕ) (hi : i ∈ oddLevels d) : (l : ℝ) ^ i * x t i ≤ D t := by
  have hnn : ∀ j ∈ oddLevels d, 0 ≤ (l : ℝ) ^ j * x t j :=
    fun j _ => mul_nonneg (by positivity) (hx.1 t j)
  have h1 : (l : ℝ) ^ i * x t i ≤ ∑ j ∈ oddLevels d, (l : ℝ) ^ j * x t j :=
    Finset.single_le_sum hnn hi
  have h2 : 0 ≤ ∑ j ∈ oddLevels d, x (t - (j : ZMod d)) j :=
    Finset.sum_nonneg fun j _ => hx.1 _ _
  have h3 := hx.2 t
  linarith
end Formalism.IncomingBounds.FlowDualityReindexing
