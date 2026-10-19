-- Prove2me | solution 2 for CohnElkies.poissonLogistic_lowerEndpointPhase_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:11:24.714101+00:00
-- url     : https://prove2.me/submissions/1fcf6f31-bed1-4e6a-9dd8-1d30206838ff

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
theorem h47_phase_bound (u : ℝ) : |lowerEndpointPhase (2 * u)| ≤ 5 * (1 + u ^ 2) := by
  unfold lowerEndpointPhase
  have ha := abs_nonneg (2 * u)
  have hat0 : 0 ≤ Real.arctan (|2 * u| / 2) := Real.arctan_nonneg.2 (by positivity)
  have hat1 : Real.arctan (|2 * u| / 2) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hl0 : 0 ≤ Real.log (1 + (2 * u) ^ 2 / 4) := Real.log_nonneg (by nlinarith [sq_nonneg (2 * u)])
  have hl1 : Real.log (1 + (2 * u) ^ 2 / 4) ≤ (2 * u) ^ 2 / 4 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (2 * u) ^ 2 / 4 by positivity)
    linarith
  have h2u : |2 * u| ≤ 1 + u ^ 2 := by
    rw [abs_mul, abs_two]; nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have hpi := Real.pi_lt_d2
  have hp := Real.pi_pos
  have hprod1 : |2 * u| / 2 * Real.arctan (|2 * u| / 2) ≤ |2 * u| / 2 * (Real.pi / 2) :=
    mul_le_mul_of_nonneg_left hat1.le (by positivity)
  have hprod0 : 0 ≤ |2 * u| / 2 * Real.arctan (|2 * u| / 2) := mul_nonneg (by positivity) hat0
  have hpa : Real.pi * |2 * u| ≤ Real.pi * (1 + u ^ 2) := mul_le_mul_of_nonneg_left h2u hp.le
  have hpb : Real.pi * (1 + u ^ 2) ≤ 3.15 * (1 + u ^ 2) :=
    mul_le_mul_of_nonneg_right hpi.le (by positivity)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg u]

theorem h47_density_bound (u : ℝ) : poissonLogisticDensity u ≤ Real.pi / (1 + u ^ 2) ^ 2 := by
  have hE := Real.exp_pos (Real.pi * u)
  have hp := Real.pi_pos
  have heq : poissonLogisticDensity u = Real.pi / (2 * (Real.cosh (Real.pi * u) + 1)) := by
    unfold poissonLogisticDensity
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  have hc4 : (Real.pi * |u|) ^ 4 / 48 ≤ Real.cosh (Real.pi * u) := by
    have h1 := Real.pow_div_factorial_le_exp (x := Real.pi * |u|) (by positivity) 4
    have h2 : Real.exp (Real.pi * |u|) / 2 ≤ Real.cosh (Real.pi * u) := by
      rw [← Real.cosh_abs, show |Real.pi * u| = Real.pi * |u| by
        rw [abs_mul, abs_of_pos hp], Real.cosh_eq]
      have := Real.exp_pos (-(Real.pi * |u|))
      linarith
    norm_num [Nat.factorial] at h1
    linarith
  have hpi4 : 48 ≤ Real.pi ^ 4 := by
    have h3 := Real.pi_gt_three
    nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) h3.le 4]
  have hu4 : (Real.pi * |u|) ^ 4 / 48 ≥ u ^ 4 := by
    have h4 : |u| ^ 4 = u ^ 4 := by
      rw [show |u| ^ 4 = (|u| ^ 2) ^ 2 by ring, sq_abs]; ring
    rw [mul_pow, h4]
    have : 0 ≤ u ^ 4 := by positivity
    nlinarith
  have hc1 := Real.one_le_cosh (Real.pi * u)
  have hkey : (1 + u ^ 2) ^ 2 ≤ 2 * (Real.cosh (Real.pi * u) + 1) := by
    nlinarith [sq_nonneg (u ^ 2 - 1)]
  rw [heq]
  apply div_le_div_of_nonneg_left hp.le (by positivity) hkey

theorem solution :
    Integrable
      (fun u : ℝ =>
        poissonLogisticDensity u *
          lowerEndpointPhase (2 * u)) := by
  have hcont : Continuous (fun u : ℝ => poissonLogisticDensity u * lowerEndpointPhase (2 * u)) := by
    unfold poissonLogisticDensity lowerEndpointPhase
    apply Continuous.mul
    · exact Continuous.div (by fun_prop) (by fun_prop) (fun u => by positivity)
    · have hlog : Continuous (fun u : ℝ => Real.log (1 + (2 * u) ^ 2 / 4)) :=
        Continuous.log (by fun_prop) (fun u => by positivity)
      have harc : Continuous (fun u : ℝ => Real.arctan (|2 * u| / 2)) :=
        Real.continuous_arctan.comp (by fun_prop)
      exact ((by fun_prop : Continuous fun u : ℝ => -Real.pi * |2 * u| / 4).sub
        (hlog.const_mul (1 / 2))).add ((by fun_prop : Continuous fun u : ℝ => |2 * u| / 2).mul harc)
  refine (integrable_inv_one_add_sq.const_mul (5 * Real.pi)).mono' hcont.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ (fun u => ?_)
  have hd := h47_density_bound u
  have hph := h47_phase_bound u
  have hd0 : 0 ≤ poissonLogisticDensity u := by unfold poissonLogisticDensity; positivity
  have hT : 0 < 1 + u ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hd0]
  calc poissonLogisticDensity u * |lowerEndpointPhase (2 * u)|
      ≤ Real.pi / (1 + u ^ 2) ^ 2 * (5 * (1 + u ^ 2)) := mul_le_mul hd hph (abs_nonneg _) (by positivity)
    _ = 5 * Real.pi * (1 + u ^ 2)⁻¹ := by field_simp

