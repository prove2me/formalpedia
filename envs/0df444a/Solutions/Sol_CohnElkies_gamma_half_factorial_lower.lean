-- Prove2me | solution 1 for CohnElkies.gamma_half_factorial_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/30e6964f-9bb1-4a4f-b116-431b2d142e3e

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
namespace CohnElkies
theorem _root_.solution (N : ℕ) :
    Real.Gamma (3 / 2 : ℝ) * (N.factorial : ℝ) ≤
      Real.Gamma ((N : ℝ) + 3 / 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hq : 0 < (N : ℝ) + 3 / 2 := by positivity
    have hrec :
        Real.Gamma (((N + 1 : ℕ) : ℝ) + 3 / 2) =
          ((N : ℝ) + 3 / 2) *
            Real.Gamma ((N : ℝ) + 3 / 2) := by
      convert! Real.Gamma_add_one hq.ne' using 1
      all_goals
        push_cast
        ring_nf
    calc
      Real.Gamma (3 / 2 : ℝ) *
          (((N + 1).factorial : ℕ) : ℝ) =
        ((N : ℝ) + 1) *
          (Real.Gamma (3 / 2 : ℝ) *
            (N.factorial : ℝ)) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
      _ ≤ ((N : ℝ) + 1) *
          Real.Gamma ((N : ℝ) + 3 / 2) :=
        mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ ((N : ℝ) + 3 / 2) *
          Real.Gamma ((N : ℝ) + 3 / 2) := by
        apply mul_le_mul_of_nonneg_right
          (by norm_num : (N : ℝ) + 1 ≤ (N : ℝ) + 3 / 2)
          (Real.Gamma_pos_of_pos hq).le
      _ = Real.Gamma (((N + 1 : ℕ) : ℝ) + 3 / 2) :=
        hrec.symm
end CohnElkies
