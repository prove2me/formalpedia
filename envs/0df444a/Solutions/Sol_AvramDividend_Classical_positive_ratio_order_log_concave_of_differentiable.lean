-- Prove2me | solution 1 for AvramDividend.Classical.positive_ratio_order_log_concave_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:47:40.765599+00:00
-- url     : https://prove2.me/submissions/c334c9d6-7b5b-4517-9fa8-69bf6f3f0a9d

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
open Filter Set Topology
open scoped Topology
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hdiff : ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (fun z : ℝ => Real.log (f z)) x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (f z)) := by
  set g : ℝ → ℝ := fun z => Real.log (f z) with hg
  -- increments of g are antitone
  have hinc : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      g (y + t) - g y ≤ g (x + t) - g x := by
    intro x y t hx hxy ht
    have hy : 0 < y := lt_of_lt_of_le hx hxy
    have h := hratio x y t hx hxy ht
    have h1 := Real.log_le_log (div_pos (hfpos x hx) (hfpos _ (by linarith))) h
    rw [Real.log_div (hfpos x hx).ne' (hfpos _ (by linarith)).ne',
      Real.log_div (hfpos y hy).ne' (hfpos _ (by linarith)).ne'] at h1
    simp only [hg]
    linarith
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0)
    (fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
    (by rw [interior_Ioi]; exact fun x hx => (hdiff x hx).differentiableWithinAt) ?_
  rw [interior_Ioi]
  intro x hx y hy hxy
  have tx := (hdiff x hx).hasDerivAt.tendsto_slope_zero_right
  have ty := (hdiff y hy).hasDerivAt.tendsto_slope_zero_right
  refine le_of_tendsto_of_tendsto ty tx ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hinc x y t hx hxy ht) (inv_nonneg.mpr ht.le)
