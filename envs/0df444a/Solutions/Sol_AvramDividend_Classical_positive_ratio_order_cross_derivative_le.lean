-- Prove2me | solution 1 for AvramDividend.Classical.positive_ratio_order_cross_derivative_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:42:55.906767+00:00
-- url     : https://prove2.me/submissions/fc9210ef-ed85-46df-bf09-2ee4f1b60f37

import Theorems.Thm_AvramDividend_Classical_positive_ratio_order_log_deriv_antitone_at_pair
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set Topology

/-- Ordered forward ratios imply a cross-multiplied derivative inequality. -/
theorem solution
    (f : ℝ → ℝ)
    (hfpos : ∀ z : ℝ, 0 < z → 0 < f z)
    (hratio : ∀ u v t : ℝ, 0 < u → u ≤ v → 0 < t →
      f u / f (u + t) ≤ f v / f (v + t))
    (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y)
    (hdx : DifferentiableAt ℝ f x)
    (hdy : DifferentiableAt ℝ f y) :
    deriv f y * f x ≤ deriv f x * f y := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxlog : HasDerivAt (fun z : ℝ => Real.log (f z))
      (deriv f x / f x) x :=
    hdx.hasDerivAt.log (ne_of_gt (hfpos x hx))
  have hylog : HasDerivAt (fun z : ℝ => Real.log (f z))
      (deriv f y / f y) y :=
    hdy.hasDerivAt.log (ne_of_gt (hfpos y hy))
  have hmono := positive_ratio_order_log_deriv_antitone_at_pair
    f hfpos hratio x y hx hxy hxlog.differentiableAt hylog.differentiableAt
  rw [hylog.deriv, hxlog.deriv] at hmono
  exact (div_le_div_iff₀ (hfpos y hy) (hfpos x hx)).mp hmono
