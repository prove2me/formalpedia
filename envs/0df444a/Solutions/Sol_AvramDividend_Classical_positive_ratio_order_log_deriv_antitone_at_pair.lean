-- Prove2me | solution 1 for AvramDividend.Classical.positive_ratio_order_log_deriv_antitone_at_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:53:43.85745+00:00
-- url     : https://prove2.me/submissions/409af782-3480-417c-a65c-96cc27e097d3

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology
open scoped Topology

/-- Local differentiability at two points suffices to compare log slopes. -/
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ z : ℝ, 0 < z → 0 < f z)
    (hratio : ∀ u v t : ℝ, 0 < u → u ≤ v → 0 < t →
      f u / f (u + t) ≤ f v / f (v + t))
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ (fun z : ℝ => Real.log (f z)) x)
    (hdy : DifferentiableAt ℝ (fun z : ℝ => Real.log (f z)) y) :
    deriv (fun z : ℝ => Real.log (f z)) y ≤
      deriv (fun z : ℝ => Real.log (f z)) x := by
  let g : ℝ → ℝ := fun z => Real.log (f z)
  change deriv g y ≤ deriv g x
  have hy : 0 < y := lt_of_lt_of_le hx hxy
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
  exact le_of_tendsto_of_tendsto
    (hdy.hasDerivAt.tendsto_slope_zero_right)
    (hdx.hasDerivAt.tendsto_slope_zero_right)
    hevent'
