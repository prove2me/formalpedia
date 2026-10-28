-- Prove2me | solution 2 for AvramDividend.Classical.positive_ratio_order_log_concave_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:47:45.861276+00:00
-- url     : https://prove2.me/submissions/9af396f1-6755-4d55-80d8-3dd768536ee2

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped Topology

/-- Positive ordered forward ratios give concavity of the log under smoothness. -/
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun z : ℝ => Real.log (f z)) x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (f z)) := by
  let g : ℝ → ℝ := fun z => Real.log (f z)
  have hanti : AntitoneOn (deriv g) (Ioi (0 : ℝ)) := by
    intro x hx y hy hxy
    change 0 < x at hx
    change 0 < y at hy
    have hevent :
        ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
          t⁻¹ * (g (y + t) - g y) ≤
          t⁻¹ * (g (x + t) - g x) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      have hxt : 0 < x + t := by linarith
      have hyt : 0 < y + t := by linarith
      have hdiv := hratio x y t hx hxy htpos
      have hlog :
          Real.log (f x / f (x + t)) ≤
          Real.log (f y / f (y + t)) :=
        Real.log_le_log (div_pos (hfpos x hx) (hfpos (x + t) hxt)) hdiv
      rw [Real.log_div (ne_of_gt (hfpos x hx))
          (ne_of_gt (hfpos (x + t) hxt)),
          Real.log_div (ne_of_gt (hfpos y hy))
          (ne_of_gt (hfpos (y + t) hyt))] at hlog
      have hinc : g (y + t) - g y ≤ g (x + t) - g x := by
        dsimp [g]
        linarith
      exact mul_le_mul_of_nonneg_left hinc (inv_nonneg.mpr (le_of_lt htpos))
    have hevent' :
        (fun t : ℝ => t⁻¹ • (g (y + t) - g y)) ≤ᶠ[𝓝[>] (0 : ℝ)]
          (fun t : ℝ => t⁻¹ • (g (x + t) - g x)) := by
      change ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        t⁻¹ • (g (y + t) - g y) ≤ t⁻¹ • (g (x + t) - g x)
      simpa only [smul_eq_mul] using hevent
    have hlimit : deriv g y ≤ deriv g x :=
      le_of_tendsto_of_tendsto
        ((hdiff y hy).hasDerivAt.tendsto_slope_zero_right)
        ((hdiff x hx).hasDerivAt.tendsto_slope_zero_right)
        hevent'
    exact hlimit
  have hcont : ContinuousOn g (Ioi (0 : ℝ)) := by
    intro x hx
    change 0 < x at hx
    exact ((hdiff x hx).continuousAt).continuousWithinAt
  have hdiffOn : DifferentiableOn ℝ g (interior (Ioi (0 : ℝ))) := by
    intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using hx
    exact (hdiff x hx').differentiableWithinAt
  have hanti' : AntitoneOn (deriv g) (interior (Ioi (0 : ℝ))) := by
    simpa only [interior_Ioi] using hanti
  exact hanti'.concaveOn_of_deriv (convex_Ioi 0) hcont hdiffOn
