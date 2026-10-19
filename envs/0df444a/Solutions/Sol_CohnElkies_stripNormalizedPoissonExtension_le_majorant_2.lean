-- Prove2me | solution 2 for CohnElkies.stripNormalizedPoissonExtension_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:08.963957+00:00
-- url     : https://prove2.me/submissions/963f94ad-c38d-4272-8afa-444222e44d17

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


theorem solution
    {σ : ℝ} (hzero : 0 ≤ σ) (hone : σ ≤ 1) (T : ℝ) :
    0 ≤ stripNormalizedPoissonExtension σ T ∧
      stripNormalizedPoissonExtension σ T ≤
        stripPoissonExponentialMajorant T := by
  unfold stripNormalizedPoissonExtension stripPoissonExponentialMajorant
  have hp := Real.pi_pos
  set θ : ℝ := Real.pi * (1 - σ) / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; have : 0 ≤ 1 - σ := by linarith
                         positivity
  have hθ1 : θ ≤ Real.pi / 2 := by rw [hθ]; nlinarith
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hθ1
  have hsinc0 : 0 ≤ Real.sinc θ := by
    rcases eq_or_lt_of_le hθ0 with h | h
    · rw [← h]; simp [Real.sinc]
    · rw [Real.sinc_of_ne_zero h.ne']
      exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)) hθ0
  have hsinc1 := Real.sinc_le_one θ
  have hch : Real.exp (|Real.pi * T / 2|) / 2 ≤ Real.cosh (Real.pi * T / 2) := by
    rw [← Real.cosh_abs, Real.cosh_eq]; have := Real.exp_pos (-|Real.pi * T / 2|); linarith
  have hab : |Real.pi * T / 2| = (Real.pi / 2) * |T| := by
    rw [show Real.pi * T / 2 = (Real.pi / 2) * T by ring, abs_mul, abs_of_pos (by positivity)]
  rw [hab] at hch
  have hE := Real.exp_pos ((Real.pi / 2) * |T|)
  have hD : 0 < Real.cosh (Real.pi * T / 2) + Real.cos θ := by
    have := Real.cosh_pos (Real.pi * T / 2); linarith
  constructor
  · positivity
  · rw [div_le_iff₀ hD]
    have hneg : Real.exp (-(Real.pi / 2) * |T|) * Real.exp ((Real.pi / 2) * |T|) = 1 := by
      rw [← Real.exp_add]; simp
    have hEn := Real.exp_pos (-(Real.pi / 2) * |T|)
    have key : 1 / 2 ≤ Real.exp (-(Real.pi / 2) * |T|) * Real.cosh (Real.pi * T / 2) := by
      have := mul_le_mul_of_nonneg_left hch hEn.le
      rw [mul_div_assoc', hneg] at this
      linarith
    have k2 := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ Real.pi / 2)
    have k3 := mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2) hEn.le) hcos
    have k4 := mul_le_mul_of_nonneg_left hsinc1 (by positivity : (0:ℝ) ≤ Real.pi / 4)
    nlinarith

