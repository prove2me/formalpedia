-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.log_maps_real_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:08:04.987105+00:00
-- url     : https://prove2.me/submissions/e03f0147-7985-499d-9e7f-a9c9ab827787

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
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_log_lipschitz_real_ball
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
    MapsTo Complex.log (ball (Complex.exp x) 8) (ball x 8) := by
  intro z hz
  have h := (log_lipschitz_real_ball hx hx10).norm_sub_le hz
    (mem_ball_self (by norm_num : (0 : ℝ) < 8))
  have heq : Complex.log (Complex.exp x) = x :=
    Complex.log_exp (by rw [hx]; linarith [Real.pi_pos]) (by rw [hx]; exact Real.pi_pos.le)
  rw [heq] at h
  have hz' : ‖z - Complex.exp x‖ < 8 := by simpa [mem_ball, dist_eq_norm] using hz
  rw [mem_ball, dist_eq_norm]
  norm_num at h
  linarith
end ExponentialJuliaSetMisiurewicz
