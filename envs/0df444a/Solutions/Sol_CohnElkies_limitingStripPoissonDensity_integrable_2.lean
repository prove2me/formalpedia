-- Prove2me | solution 2 for CohnElkies.limitingStripPoissonDensity_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:02:09.5034+00:00
-- url     : https://prove2.me/submissions/02e6972f-dc2d-414e-acb5-0a5530dfe41c

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
theorem h47_cosh_ge (x : ℝ) : 1 + x ^ 2 / 4 ≤ Real.cosh x := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 := Real.quadratic_le_exp_of_nonneg (abs_nonneg x)
  have h2 := Real.add_one_le_exp (-|x|)
  have h3 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith

theorem solution :
    Integrable limitingStripPoissonDensity := by
  have hp := Real.pi_pos
  have hpi2 : 8 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  refine (integrable_inv_one_add_sq.const_mul (Real.pi / 2)).mono' ?_ ?_
  · have hden : ∀ T : ℝ, 0 < 4 * (Real.cosh (Real.pi * T / 2) + 1) := by
      intro T; have := Real.one_le_cosh (Real.pi * T / 2); linarith
    unfold limitingStripPoissonDensity
    exact (Continuous.div continuous_const (by fun_prop) (fun T => (hden T).ne')).aestronglyMeasurable
  · refine MeasureTheory.ae_of_all _ (fun T => ?_)
    unfold limitingStripPoissonDensity
    have hc := h47_cosh_ge (Real.pi * T / 2)
    have hpos : 0 < 4 * (Real.cosh (Real.pi * T / 2) + 1) := by
      have := Real.one_le_cosh (Real.pi * T / 2); linarith
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hp hpos), div_le_iff₀ hpos]
    have hT : 0 < 1 + T ^ 2 := by positivity
    have hkey : (1 + T ^ 2) ≤ 2 * (Real.cosh (Real.pi * T / 2) + 1) := by
      have : (Real.pi * T / 2) ^ 2 = Real.pi ^ 2 * T ^ 2 / 4 := by ring
      rw [this] at hc
      nlinarith [sq_nonneg T]
    have hinv : (1 + T ^ 2)⁻¹ * (1 + T ^ 2) = 1 := inv_mul_cancel₀ hT.ne'
    have hi := inv_pos.2 hT
    nlinarith [mul_le_mul_of_nonneg_left hkey hi.le]

