-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb23_original_discounted_zero_contact_budget_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:37:15.434045+00:00
-- url     : https://prove2.me/submissions/ee159ab9-0a1e-4c39-97d0-230bebb567f1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (q T : ℝ) (hq : 0 < q) (hT : 0 ≤ T) :
    q * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) = 1 := by
  have hd :
      deriv (fun y : ℝ => Real.exp ((-q) * y)) =
        (fun y : ℝ => (-q) * Real.exp ((-q) * y)) := by
    funext y
    have he : HasDerivAt (fun z : ℝ => Real.exp ((-q) * z))
        (Real.exp ((-q) * y) * (-q)) y := by
      simpa only [mul_one, id_eq] using (((hasDerivAt_id y).const_mul (-q)).exp)
    simpa only [mul_comm] using he.deriv
  have hFTC :
      (∫ y in (0 : ℝ)..T, (-q) * Real.exp ((-q) * y)) =
        Real.exp ((-q) * T) - Real.exp ((-q) * (0 : ℝ)) := by
    exact intervalIntegral.integral_deriv_eq_sub'
      (fun y : ℝ => Real.exp ((-q) * y)) hd
      (by intro y hy; fun_prop) (by fun_prop)
  rw [intervalIntegral.integral_const_mul] at hFTC
  simp only [mul_zero, Real.exp_zero] at hFTC
  nlinarith
