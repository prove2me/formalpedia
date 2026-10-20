-- Prove2me | solution 2 for CohnElkies.saddleExpSeries_tail_term_le_geometric
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:52.721605+00:00
-- url     : https://prove2.me/submissions/1e410dce-be9b-42ba-8f63-9f7add254c96

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
    (m : ℕ) (hym : 2 * y ≤ (m : ℝ) + 1)
    (k : ℕ) :
    y ^ (m + k) / ((m + k).factorial : ℝ) ≤
      (y ^ m / (m.factorial : ℝ)) *
        ((1 / 2 : ℝ) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have key : y ^ (m + (k+1)) / ((m + (k+1)).factorial : ℝ) =
        (y ^ (m + k) / ((m + k).factorial : ℝ)) * (y / ((m:ℝ) + k + 1)) := by
      rw [show m + (k+1) = (m+k) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [key, pow_succ]
    have hk : (0:ℝ) ≤ k := k.cast_nonneg
    have hq : y / ((m:ℝ) + k + 1) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hq0 : 0 ≤ y / ((m:ℝ) + k + 1) := by positivity
    calc _ ≤ (y ^ m / (m.factorial : ℝ) * (1/2)^k) * (y / ((m:ℝ) + k + 1)) :=
          mul_le_mul_of_nonneg_right ih hq0
      _ ≤ (y ^ m / (m.factorial : ℝ) * (1/2)^k) * (1/2) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
      _ = _ := by ring

