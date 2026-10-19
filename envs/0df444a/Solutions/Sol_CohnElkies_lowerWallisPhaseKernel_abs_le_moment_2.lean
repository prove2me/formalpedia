-- Prove2me | solution 2 for CohnElkies.lowerWallisPhaseKernel_abs_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:18:11.33037+00:00
-- url     : https://prove2.me/submissions/6ee6e55a-8a25-4bf0-bdd2-3f4d90661b56

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
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisPhaseKernel u t| ≤ |u| + 1 := by
  unfold lowerWallisPhaseKernel
  have ht2 : 0 < t ^ 2 := by positivity
  rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
  have hE0 : 0 < Real.exp (-t) := Real.exp_pos _
  have hE1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have hE2 : Real.exp (-t) * (1 + t) ≤ 1 := by
    have h := Real.add_one_le_exp t
    have : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have hEle : Real.exp (-t) ≤ 1 := by nlinarith
  have hc : |Real.cos (u * t) - 1| ≤ |u| * t := by
    have h1 : 1 - Real.cos (u * t) ≤ (u * t) ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := u * t)]
    have h2 : 0 ≤ 1 - Real.cos (u * t) := by linarith [Real.cos_le_one (u * t)]
    have h3 : 1 - Real.cos (u * t) ≤ 2 := by linarith [Real.neg_one_le_cos (u * t)]
    have hx : |u * t| = |u| * t := by rw [abs_mul, abs_of_pos ht]
    rw [abs_sub_comm, abs_of_nonneg h2, ← hx]
    rcases le_total |u * t| 2 with h | h
    · have : (u * t) ^ 2 = |u * t| ^ 2 := (sq_abs _).symm
      nlinarith [abs_nonneg (u * t)]
    · linarith
  have hA0 : 0 ≤ 1 - Real.exp (-t) - t * Real.exp (-t) := by nlinarith
  have hA1 : 1 - Real.exp (-t) - t * Real.exp (-t) ≤ t ^ 2 := by nlinarith
  have hB : |(1 - Real.exp (-t)) * (Real.cos (u * t) - 1)| ≤ t * (|u| * t) := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - Real.exp (-t))]
    exact mul_le_mul (by linarith) hc (abs_nonneg _) ht.le
  have e : (1 - Real.exp (-t)) * Real.cos (u * t) - t * Real.exp (-t) =
      (1 - Real.exp (-t) - t * Real.exp (-t)) + (1 - Real.exp (-t)) * (Real.cos (u * t) - 1) := by ring
  rw [e]
  calc |(1 - Real.exp (-t) - t * Real.exp (-t)) + (1 - Real.exp (-t)) * (Real.cos (u * t) - 1)|
      ≤ |1 - Real.exp (-t) - t * Real.exp (-t)| + |(1 - Real.exp (-t)) * (Real.cos (u * t) - 1)| :=
        abs_add_le _ _
    _ ≤ t ^ 2 + t * (|u| * t) := by rw [abs_of_nonneg hA0]; linarith
    _ = (|u| + 1) * t ^ 2 := by ring

