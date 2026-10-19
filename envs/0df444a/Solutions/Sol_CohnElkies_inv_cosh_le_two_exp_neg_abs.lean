-- Prove2me | solution 1 for CohnElkies.inv_cosh_le_two_exp_neg_abs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/8b18d0ea-9591-485c-b72d-ab5a03db4ea9

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
namespace CohnElkies
theorem _root_.solution (u : ℝ) :
    (Real.cosh u)⁻¹ ≤ 2 * Real.exp (-|u|) := by
  have hhalf : Real.exp |u| / 2 ≤ Real.cosh u := by
    rw [← Real.cosh_abs, Real.cosh_eq]
    have hpositive := (Real.exp_pos (-|u|)).le
    linarith
  rw [← one_div, div_le_iff₀ (Real.cosh_pos u)]
  calc
    (1 : ℝ) =
        (2 * Real.exp (-|u|)) * (Real.exp |u| / 2) := by
      calc
        (1 : ℝ) = Real.exp (-|u|) * Real.exp |u| := by
          rw [← Real.exp_add]
          simp
        _ = (2 * Real.exp (-|u|)) * (Real.exp |u| / 2) := by
          ring
    _ ≤ (2 * Real.exp (-|u|)) * Real.cosh u :=
      mul_le_mul_of_nonneg_left hhalf (by positivity)
end CohnElkies
