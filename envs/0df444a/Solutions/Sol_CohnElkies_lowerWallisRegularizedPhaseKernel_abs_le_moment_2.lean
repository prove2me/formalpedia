-- Prove2me | solution 2 for CohnElkies.lowerWallisRegularizedPhaseKernel_abs_le_moment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:38:55.054984+00:00
-- url     : https://prove2.me/submissions/dbb6d38c-eb47-4f66-8391-a22e6b7a7dc3

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
    {a : ℝ} (hazero : 0 ≤ a) (haone : a ≤ 1)
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    |lowerWallisRegularizedPhaseKernel a u t| ≤ |u| + 2 := by
  unfold lowerWallisRegularizedPhaseKernel
  set E := Real.exp (-t) with hEdef
  set F := Real.exp (-a * t) with hFdef
  set C := Real.cos (u * t) with hCdef
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEl : 1 - t ≤ E := by have := Real.add_one_le_exp (-t); linarith
  have hEu : E * (1 + t) ≤ 1 := by
    have h1 := Real.add_one_le_exp t
    have h2 : E * Real.exp t = 1 := by rw [hEdef, ← Real.exp_add]; simp
    nlinarith
  have hF0 : 0 < F := Real.exp_pos _
  have hF1 : F ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hFl : 1 - a * t ≤ F := by have := Real.add_one_le_exp (-a * t); linarith
  have hC1 : |C| ≤ 1 := Real.abs_cos_le_one _
  have hCl : 1 - C ≤ |u| * t := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := u * t)
    have h2 := Real.cos_le_one (u * t)
    have h3 := Real.neg_one_le_cos (u * t)
    have hut : |u * t| = |u| * t := by rw [abs_mul, abs_of_pos ht]
    rcases le_or_gt (|u * t|) 2 with h | h
    · have : (u * t) ^ 2 = |u * t| ^ 2 := (sq_abs _).symm
      nlinarith [abs_nonneg (u * t)]
    · linarith
  have hFC : |F * C - 1| ≤ (1 + |u|) * t := by
    have : F * C - 1 = (F - 1) * C + (C - 1) := by ring
    rw [this]
    calc |(F - 1) * C + (C - 1)| ≤ |(F - 1) * C| + |C - 1| := abs_add_le _ _
      _ = |F - 1| * |C| + |C - 1| := by rw [abs_mul]
      _ ≤ |F - 1| * 1 + |C - 1| := by gcongr
      _ ≤ a * t + |u| * t := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith [Real.cos_le_one (u*t)])]
          linarith
      _ ≤ (1 + |u|) * t := by nlinarith [abs_nonneg u]
  have hnum : |(1 - E) * F * C - t * E| ≤ (|u| + 2) * t ^ 2 := by
    have : (1 - E) * F * C - t * E = (1 - E - t * E) * (F * C) + t * E * (F * C - 1) := by ring
    rw [this]
    have hA : 0 ≤ 1 - E - t * E := by nlinarith
    have hFCa : |F * C| ≤ 1 := by rw [abs_mul, abs_of_pos hF0]; nlinarith [abs_nonneg C]
    have hB : 1 - E - t * E + t ^ 2 * E * (1 + |u|) ≤ (|u| + 2) * t ^ 2 := by
      rcases le_or_gt t 1 with h | h
      · have : 0 ≤ 1 + t - t ^ 2 := by nlinarith
        have : 1 - E - t * E + t ^ 2 * E ≤ 2 * t ^ 2 := by nlinarith [mul_le_mul_of_nonneg_right hEl this]
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg t) (abs_nonneg u)) (sub_nonneg.2 hE1)]
      · have : t ^ 2 * E * (1 + |u|) ≤ t ^ 2 * (1 + |u|) := by
          have := abs_nonneg u
          have h0 : 0 ≤ t ^ 2 * (1 + |u|) := by positivity
          nlinarith
        nlinarith [abs_nonneg u]
    calc |(1 - E - t * E) * (F * C) + t * E * (F * C - 1)|
        ≤ |(1 - E - t * E) * (F * C)| + |t * E * (F * C - 1)| := abs_add_le _ _
      _ = (1 - E - t * E) * |F * C| + t * E * |F * C - 1| := by
          rw [abs_mul (1 - E - t * E), abs_mul (t * E), abs_of_nonneg hA, abs_of_pos (by positivity : 0 < t * E)]
      _ ≤ (1 - E - t * E) * 1 + t * E * ((1 + |u|) * t) := by gcongr
      _ = 1 - E - t * E + t ^ 2 * E * (1 + |u|) := by ring
      _ ≤ (|u| + 2) * t ^ 2 := hB
  have ht2 : 0 < t ^ 2 := by positivity
  rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
  exact hnum

