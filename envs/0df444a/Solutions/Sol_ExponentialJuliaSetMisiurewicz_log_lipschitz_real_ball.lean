-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.log_lipschitz_real_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:03:11.544897+00:00
-- url     : https://prove2.me/submissions/3564ad09-2c52-4f7d-9e64-24633fdfb214

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_ExpChaotic_Covering
import Definitions.Def_ExpChaotic_Periodic
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {x : ℂ} (hx : x.im = 0) (hx10 : 10 ≤ x.re) :
    LipschitzOnWith (1 / 2) Complex.log (ball (Complex.exp x) 8) := by
  have hrez : ∀ z ∈ ball (Complex.exp x) 8, (2 : ℝ) ≤ z.re := by
    intro z hz
    have hdist : ‖z - Complex.exp x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
    have h := (Complex.abs_re_le_norm (z - Complex.exp x)).trans_lt hdist
    simp only [Complex.sub_re, Complex.exp_re, hx, Real.cos_zero, mul_one] at h
    linarith [(abs_lt.mp h).1, Real.add_one_le_exp x.re]
  have hslit : ∀ z ∈ ball (Complex.exp x) 8, z ∈ Complex.slitPlane := by
    intro z hz
    exact Or.inl (by linarith [hrez z hz])
  apply (convex_ball (Complex.exp x) 8).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun z hz => (Complex.hasDerivAt_log (hslit z hz)).hasDerivWithinAt)
  intro z hz
  change ‖z⁻¹‖ ≤ (1 / 2 : ℝ)
  rw [norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) ((hrez z hz).trans (Complex.re_le_norm z))
end ExponentialJuliaSetMisiurewicz
