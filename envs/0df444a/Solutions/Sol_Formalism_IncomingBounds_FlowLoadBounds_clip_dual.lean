-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.clip_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:07.540471+00:00
-- url     : https://prove2.me/submissions/b90003c8-0939-46b9-ad86-365e101895fa

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
theorem _root_.solution (hl : 1 ≤ l) {τ : ZMod d → ℝ} (h0 : ∀ s, 0 ≤ τ s)
    (h1 : ∀ s, ∀ i ∈ oddLevels d, 1 ≤ (l : ℝ) ^ i * τ s + τ (s + (i : ZMod d))) :
    IsDual l d (fun s => min (τ s) 1) := by
  refine ⟨fun s => ⟨le_min (h0 s) zero_le_one, min_le_right _ _⟩, fun s i hi => ?_⟩
  show 1 ≤ (l : ℝ) ^ i * min (τ s) 1 + min (τ (s + (i : ZMod d))) 1
  have hl' : (1 : ℝ) ≤ (l : ℝ) ^ i := by
    have h : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact one_le_pow₀ h
  have hτ := h1 s i hi
  have hp : 0 ≤ (l : ℝ) ^ i * τ s := mul_nonneg (by positivity) (h0 s)
  have hq := h0 (s + (i : ZMod d))
  rcases le_total (τ s) 1 with h | h <;> rcases le_total (τ (s + (i : ZMod d))) 1 with h' | h'
  · rw [min_eq_left h, min_eq_left h']
    exact hτ
  · rw [min_eq_left h, min_eq_right h']
    linarith
  · rw [min_eq_right h, min_eq_left h']
    linarith
  · rw [min_eq_right h, min_eq_right h']
    linarith
end Formalism.IncomingBounds.FlowLoadBounds
