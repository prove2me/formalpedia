-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_alternating_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:40:04.45271+00:00
-- url     : https://prove2.me/submissions/068ea91f-ced2-4666-a7ea-799fe6d86b50

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {y : ℝ} (hy : 0 ≤ y)
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1) :
    |Real.exp (-y) -
        (∑ n ∈ Finset.range m,
          (-y) ^ n / (n.factorial : ℝ))| ≤
      2 * (y ^ m / (m.factorial : ℝ)) := by
  have hx : ‖((-y : ℝ) : ℂ)‖ / (m.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hy]
    have : (0:ℝ) < m.succ := by positivity
    rw [div_le_iff₀ this]; push_cast; linarith
  have h := Complex.exp_bound' hx
  have hc : Complex.exp ((-y : ℝ) : ℂ) - ∑ n ∈ Finset.range m, ((-y : ℝ) : ℂ) ^ n / (n.factorial : ℂ)
      = ((Real.exp (-y) - ∑ n ∈ Finset.range m, (-y) ^ n / (n.factorial : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg hy] at h
  linarith

