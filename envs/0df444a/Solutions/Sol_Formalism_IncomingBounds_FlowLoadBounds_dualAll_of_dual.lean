-- Prove2me | solution 1 for Formalism.IncomingBounds.FlowLoadBounds.dualAll_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:08.092905+00:00
-- url     : https://prove2.me/submissions/67231935-6c69-4637-b0db-edde43ded264

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
theorem _root_.solution (hl : 1 ≤ l) (hev : Even d) {σ : ZMod d → ℝ} (h : IsDual l d σ) :
    IsDualAll l d σ := by
  intro s i hi
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hr : i % d ∈ oddLevels d := by
    simp only [oddLevels, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    rw [Nat.odd_iff, Nat.mod_mod_of_dvd _ (even_iff_two_dvd.mp hev)]
    exact Nat.odd_iff.mp hi
  have h1 := h.2 s (i % d) hr
  rw [ZMod.natCast_mod] at h1
  have hpow : (l : ℝ) ^ (i % d) ≤ (l : ℝ) ^ i := by
    have h' : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
    exact pow_le_pow_right₀ h' (Nat.mod_le i d)
  have h2 := mul_le_mul_of_nonneg_right hpow (h.1 s).1
  linarith
end Formalism.IncomingBounds.FlowLoadBounds
