-- Prove2me | solution 1 for FriedCrossing.Hadamard.entry_slope_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:52.524672+00:00
-- url     : https://prove2.me/submissions/fa905b1c-1365-497b-b13b-24cb45f82239

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.Hadamard
namespace FriedCrossing.Hadamard
theorem _root_.solution {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : ∃ ξ, |ξ| < |τ| ∧ (f τ - f 0) / τ = f' ξ := by
  have hcont : ∀ s, ContinuousAt f s := fun s => (hderiv s).continuousAt
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hneg
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg hξ.2]; linarith [hξ.1]
    · rw [hslope, zero_sub, div_neg, ← neg_div, neg_sub]
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos hξ.1]; exact hξ.2
    · rw [hslope, sub_zero]
end FriedCrossing.Hadamard
