-- Prove2me | solution 2 for CohnElkies.lower_abs_log_coth_div_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:21:03.349584+00:00
-- url     : https://prove2.me/submissions/2d5467e6-8e0b-422b-98ae-876442657235

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution {x : ℝ} (hx : 0 < x) :
    |Real.log (lowerCoth (Real.pi * x) / x)| ≤
      2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
  have hpi := Real.pi_pos
  have hy : 0 < Real.pi * x := mul_pos hpi hx
  unfold lowerCoth
  have hs : 0 < Real.sinh (Real.pi * x) := Real.sinh_pos_iff.2 hy
  have hcs : Real.sinh (Real.pi * x) ≤ Real.cosh (Real.pi * x) := (Real.sinh_lt_cosh _).le
  have hc1 : 1 ≤ Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) := (one_le_div hs).2 hcs
  have hcu : Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x) ≤ (Real.pi * x + 1) / (Real.pi * x) := by
    rw [div_le_div_iff₀ hs hy, Real.cosh_eq, Real.sinh_eq]
    have hE := Real.exp_pos (Real.pi * x)
    have hF := Real.exp_pos (-(Real.pi * x))
    have hEF : Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = 1 := by rw [← Real.exp_add]; simp
    have h2 : 2 * (Real.pi * x) + 1 ≤ Real.exp (Real.pi * x) * Real.exp (Real.pi * x) := by
      rw [← Real.exp_add]; linarith [Real.add_one_le_exp (Real.pi * x + Real.pi * x)]
    have h3 : Real.exp (Real.pi * x) * Real.exp (Real.pi * x) * Real.exp (-(Real.pi * x)) = Real.exp (Real.pi * x) := by
      rw [mul_assoc, hEF, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left h2 hF.le, mul_pos hF hy]
  have hlogc : Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) ≤ Real.pi * x - Real.log Real.pi - Real.log x := by
    have h1 := Real.log_le_log (by linarith) hcu
    rw [Real.log_div (by linarith) hy.ne', Real.log_mul hpi.ne' hx.ne'] at h1
    have h2 : Real.log (Real.pi * x + 1) ≤ Real.pi * x := by
      have := Real.log_le_sub_one_of_pos (show 0 < Real.pi * x + 1 by linarith); linarith
    linarith
  have hlogc0 : 0 ≤ Real.log (Real.cosh (Real.pi * x) / Real.sinh (Real.pi * x)) := Real.log_nonneg hc1
  rw [Real.log_div (by linarith) hx.ne', abs_le]
  constructor <;> linarith [le_abs_self (Real.log Real.pi), neg_abs_le (Real.log Real.pi), le_abs_self (Real.log x), neg_abs_le (Real.log x)]

