-- Prove2me | solution 2 for CohnElkies.gamma_half_factorial_lower
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:13:05.667582+00:00
-- url     : https://prove2.me/submissions/39ee3692-2e8b-4ab7-a9db-220f930bc6e7

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators


theorem solution (N : ℕ) :
    Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ) ≤
      Real.Gamma ((N : ℝ) + 3 / 2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hg : 0 < Real.Gamma (3/2 : ℝ) := Real.Gamma_pos_of_pos (by norm_num)
    have e : ((n + 1 : ℕ) : ℝ) + 3 / 2 = ((n : ℝ) + 3 / 2) + 1 := by push_cast; ring
    rw [e, Real.Gamma_add_one (by positivity), Nat.factorial_succ]
    push_cast
    have hf : (0:ℝ) ≤ (n.factorial : ℝ) := by positivity
    have hn : (0:ℝ) ≤ n := n.cast_nonneg
    nlinarith [mul_nonneg hg.le hf]

