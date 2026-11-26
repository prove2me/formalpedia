-- Prove2me | solution 1 for FriedCrossing.HQuot.slope_eq_strict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:20.705011+00:00
-- url     : https://prove2.me/submissions/46cde813-72dc-45fa-b375-9cbd8549d30f

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.HQuot
namespace FriedCrossing.HQuot
theorem _root_.solution {f f' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt f (f' t) t) {τ : ℝ}
    (hτ : τ ≠ 0) : ∃ ξ, ξ ≠ 0 ∧ |ξ| < |τ| ∧ (f τ - f 0) / τ = f' ξ := by
  have hcont : ∀ s, ContinuousAt f s := fun s => (hderiv s).continuousAt
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hneg
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, hξ.2.ne, ?_, ?_⟩
    · rw [abs_of_neg hneg, abs_of_neg hξ.2]; linarith [hξ.1]
    · rw [hslope, zero_sub, div_neg, ← neg_div, neg_sub]
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hpos
      (fun s _ => (hcont s).continuousWithinAt) (fun s _ => hderiv s)
    refine ⟨ξ, hξ.1.ne', ?_, ?_⟩
    · rw [abs_of_pos hpos, abs_of_pos hξ.1]; exact hξ.2
    · rw [hslope, sub_zero]
end FriedCrossing.HQuot
