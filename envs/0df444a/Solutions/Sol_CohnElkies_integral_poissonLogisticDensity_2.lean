-- Prove2me | solution 2 for CohnElkies.integral_poissonLogisticDensity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:54.593475+00:00
-- url     : https://prove2.me/submissions/a33e752f-782b-41ce-bc3d-9c15ffc7eff9

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


theorem solution :
    (∫ u : ℝ, poissonLogisticDensity u) = 1 := by
  have hpi := Real.pi_pos
  have hP : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.exp (Real.pi * u) / (1 + Real.exp (Real.pi * u)))
      (poissonLogisticDensity u) u := by
    intro u
    have he : HasDerivAt (fun u : ℝ => Real.exp (Real.pi * u)) (Real.exp (Real.pi * u) * Real.pi) u := by
      simpa using ((hasDerivAt_id u).const_mul Real.pi).exp
    have h1 : (1 + Real.exp (Real.pi * u)) ≠ 0 := by positivity
    have := he.div (he.const_add 1) h1
    exact this.congr_deriv (by unfold poissonLogisticDensity; field_simp <;> ring)
  have hEtop : Tendsto (fun u : ℝ => Real.exp (Real.pi * u)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hpi)
  have hEbot : Tendsto (fun u : ℝ => Real.exp (Real.pi * u)) atBot (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot hpi)
  have htop : Tendsto (fun u : ℝ => Real.exp (Real.pi * u) / (1 + Real.exp (Real.pi * u))) atTop (𝓝 1) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 hEtop)).const_sub (1:ℝ)
    rw [sub_zero] at h
    refine h.congr fun u => ?_
    have : (1 + Real.exp (Real.pi * u)) ≠ 0 := by positivity
    simp only [Function.comp]
    field_simp
    ring
  have hbot : Tendsto (fun u : ℝ => Real.exp (Real.pi * u) / (1 + Real.exp (Real.pi * u))) atBot (𝓝 0) := by
    have h := hEbot.div (hEbot.const_add 1) (by norm_num)
    rw [add_zero, zero_div] at h
    exact h
  have hint : Integrable poissonLogisticDensity := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 * Real.pi)) ?_ (ae_of_all _ fun u => ?_)
    · apply Continuous.aestronglyMeasurable
      unfold poissonLogisticDensity
      have : ∀ u : ℝ, (1 + Real.exp (Real.pi * u)) ^ 2 ≠ 0 := fun u => by positivity
      exact Continuous.div (by fun_prop) (by fun_prop) this
    · have hE := Real.exp_pos (Real.pi * u)
      have hρ : 0 ≤ poissonLogisticDensity u := by unfold poissonLogisticDensity; positivity
      rw [Real.norm_of_nonneg hρ]
      unfold poissonLogisticDensity
      have key : Real.exp (Real.pi * u) * (1 + u ^ 2) ≤ 2 * (1 + Real.exp (Real.pi * u)) ^ 2 := by
        rcases le_total 0 u with hu | hu
        · have q := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ Real.pi * u)
          have hpu : u ^ 2 ≤ (Real.pi * u) ^ 2 := by
            rw [mul_pow]; nlinarith [mul_nonneg (by nlinarith [Real.pi_gt_three] : (0:ℝ) ≤ Real.pi ^ 2 - 1) (sq_nonneg u)]
          have h2 : 1 + u ^ 2 ≤ 2 * Real.exp (Real.pi * u) := by nlinarith [mul_nonneg hpi.le hu]
          nlinarith [mul_le_mul_of_nonneg_left h2 hE.le]
        · have q := Real.quadratic_le_exp_of_nonneg (by nlinarith : 0 ≤ Real.pi * (-u))
          have hEF : Real.exp (Real.pi * u) * Real.exp (Real.pi * (-u)) = 1 := by
            rw [← Real.exp_add]; simp
          have hpu : u ^ 2 ≤ (Real.pi * (-u)) ^ 2 := by
            rw [mul_pow, neg_sq]; nlinarith [mul_nonneg (by nlinarith [Real.pi_gt_three] : (0:ℝ) ≤ Real.pi ^ 2 - 1) (sq_nonneg u)]
          have h2 : 1 + u ^ 2 ≤ 2 * Real.exp (Real.pi * (-u)) := by nlinarith [mul_nonneg hpi.le (neg_nonneg.2 hu)]
          nlinarith [mul_le_mul_of_nonneg_left h2 hE.le]
      have : 2 * Real.pi * (1 + u ^ 2)⁻¹ - Real.pi * Real.exp (Real.pi * u) / (1 + Real.exp (Real.pi * u)) ^ 2
          = Real.pi * (2 * (1 + Real.exp (Real.pi * u)) ^ 2 - Real.exp (Real.pi * u) * (1 + u ^ 2)) /
            ((1 + u ^ 2) * (1 + Real.exp (Real.pi * u)) ^ 2) := by
        field_simp <;> ring
      linarith [div_nonneg (mul_nonneg hpi.le (sub_nonneg.2 key)) (by positivity : (0:ℝ) ≤ (1 + u ^ 2) * (1 + Real.exp (Real.pi * u)) ^ 2)]
  rw [integral_of_hasDerivAt_of_tendsto hP hint hbot htop]
  norm_num

