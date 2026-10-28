-- Prove2me | solution 1 for AvramDividend.Classical.concave_log_of_antitone_log_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:32:47.570996+00:00
-- url     : https://prove2.me/submissions/d2036853-d4c1-4da4-aba1-fa099b2616ec

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (V : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x)
    (hanti : AntitoneOn (fun x : ℝ => deriv V x / V x) (Ioi (0 : ℝ))) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (V x)) := by
  have hlog : ∀ x : ℝ, 0 < x →
      HasDerivAt (fun y : ℝ => Real.log (V y)) (deriv V x / V x) x := by
    intro x hx
    convert (Real.hasDerivAt_log (ne_of_gt (hpos x hx))).comp x (hderiv x hx)
      using 1 <;> (first | rfl | ring)
  have hcont : ContinuousOn (fun x : ℝ => Real.log (V x)) (Ioi 0) := by
    intro x hx
    exact (hlog x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => Real.log (V x))
      (interior (Ioi (0 : ℝ))) := by
    rw [interior_Ioi]
    intro x hx
    exact (hlog x hx).differentiableAt.differentiableWithinAt
  apply AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) hcont hdiff
  intro x hx y hy hxy
  rw [interior_Ioi] at hx hy
  rw [(hlog x hx).deriv, (hlog y hy).deriv]
  exact hanti hx hy hxy
