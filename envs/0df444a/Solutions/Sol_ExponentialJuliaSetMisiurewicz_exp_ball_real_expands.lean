-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.exp_ball_real_expands
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:06:02.616381+00:00
-- url     : https://prove2.me/submissions/a9b7072d-992c-427d-9709-418247bb1556

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_RealAxis
import Definitions.Def_ExpChaotic_Covering
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma3_ball_image_of_deriv_lower_bound
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {x : ℂ} (hx : x.im = 0)
    {r m : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hm : 0 ≤ m)
    (hxm : m ≤ x.re) :
    ball (Complex.exp x) (r * m) ⊆ Complex.exp '' ball x r := by
  -- On this small real-centred disk, exp is injective and its derivative has norm at least m.
  apply lemma3_ball_image_of_deriv_lower_bound hr hm
    Complex.continuous_exp.continuousOn Complex.differentiable_exp.differentiableOn
  · intro a ha b hb hab
    have haim : |a.im| < 1 := by
      have h := (Complex.abs_im_le_norm (a - x)).trans_lt
        (show ‖a - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using ha)
      simpa [Complex.sub_im, hx] using h.trans_le hr1
    have hbim : |b.im| < 1 := by
      have h := (Complex.abs_im_le_norm (b - x)).trans_lt
        (show ‖b - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using hb)
      simpa [Complex.sub_im, hx] using h.trans_le hr1
    apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ hab <;>
      linarith [abs_lt.mp haim, abs_lt.mp hbim, Real.pi_gt_three]
  · intro z hz
    rw [Complex.deriv_exp, Complex.norm_exp]
    have h := (Complex.abs_re_le_norm (z - x)).trans_lt
      (show ‖z - x‖ < r by simpa [Metric.mem_ball, dist_eq_norm] using hz)
    have hre : x.re - r < z.re := by
      have := (abs_lt.mp h).1
      simp only [Complex.sub_re] at this
      linarith
    linarith [Real.add_one_le_exp z.re]
end ExponentialJuliaSetMisiurewicz
