-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowDualityReindexing.cs_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:11.914188+00:00
-- url     : https://prove2.me/submissions/8a45c958-0a0f-43a6-9240-749f5ba9f4c0

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_LemmaFd
import Theorems.Thm_Formalism_IncomingBounds_FlowDualityReindexing_cs_identity

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
theorem _root_.solution (D sig : ZMod d → ℝ) (x : ZMod d → ℕ → ℝ) (hx : IsFlow l d D x)
    (hs : IsDual l d sig) (heq : flowVal d x = ∑ s : ZMod d, D s * sig s) :
    (∀ s : ZMod d, sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
        (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) = 0) ∧
    (∀ s : ZMod d, ∀ i ∈ oddLevels d,
        x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) = 0) := by
  have hid := cs_identity (l := l) D sig x
  rw [heq, sub_self] at hid
  have h1 : ∀ s : ZMod d, 0 ≤ sig s * (D s - ((∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) +
      (∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i))) :=
    fun s => mul_nonneg (hs.1 s).1 (sub_nonneg.2 (hx.2 s))
  have h2 : ∀ s : ZMod d, ∀ i ∈ oddLevels d,
      0 ≤ x s i * ((l : ℝ) ^ i * sig s + sig (s + (i : ZMod d)) - 1) :=
    fun s i hi => mul_nonneg (hx.1 s i) (sub_nonneg.2 (hs.2 s i hi))
  have hA := Finset.sum_nonneg (fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => h1 s)
  have hB := Finset.sum_nonneg
    (fun s (_ : s ∈ (Finset.univ : Finset (ZMod d))) => Finset.sum_nonneg (h2 s))
  have hA0 := le_antisymm (by linarith) hA
  have hB0 := le_antisymm (by linarith) hB
  refine ⟨fun s => (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => h1 s)).1 hA0 s
    (Finset.mem_univ _), fun s i hi => ?_⟩
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun s _ => Finset.sum_nonneg (h2 s))).1 hB0 s
    (Finset.mem_univ _)
  exact (Finset.sum_eq_zero_iff_of_nonneg (h2 s)).1 this i hi
end Formalism.IncomingBounds.FlowDualityReindexing
