-- Prove2me | solution 2 for CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:32:08.006587+00:00
-- url     : https://prove2.me/submissions/49209c02-a7c1-4cea-b8ed-d4e7f765e56f

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
theorem h47_abs_sub_le (X Y : ℝ) : |X - Y| ≤ |X| + |Y| :=
  abs_le.mpr ⟨by linarith [neg_abs_le X, le_abs_self Y], by linarith [le_abs_self X, neg_abs_le Y]⟩

theorem solution
    {a : ℝ} (hazero : 0 ≤ a)
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  unfold lowerWallisRegularizedPhaseKernel
  have ht0 : 0 < t := by linarith
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hea : Real.exp (-a * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hea0 : 0 < Real.exp (-a * t) := Real.exp_pos _
  have hc := Real.abs_cos_le_one (u * t)
  have hA : |(1 - Real.exp (-t)) * Real.exp (-a * t) * Real.cos (u * t)| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - Real.exp (-t)), abs_of_pos hea0]
    have h1 : (1 - Real.exp (-t)) * Real.exp (-a * t) ≤ 1 := by nlinarith
    calc _ ≤ (1 - Real.exp (-t)) * Real.exp (-a * t) * 1 :=
          mul_le_mul_of_nonneg_left hc (mul_nonneg (by linarith) hea0.le)
      _ ≤ 1 := by linarith
  have hnum := h47_abs_sub_le ((1 - Real.exp (-t)) * Real.exp (-a * t) * Real.cos (u * t))
    (t * Real.exp (-t))
  rw [abs_of_pos (by positivity : 0 < t * Real.exp (-t))] at hnum
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2), div_le_iff₀ (by positivity)]
  have e : (1 / t ^ 2 + Real.exp (-t)) * t ^ 2 = 1 + Real.exp (-t) * t ^ 2 := by field_simp
  rw [e]
  have h2 : t * Real.exp (-t) ≤ Real.exp (-t) * t ^ 2 := by
    have := mul_le_mul_of_nonneg_left (show t ≤ t ^ 2 by nlinarith) he.le
    linarith
  linarith

