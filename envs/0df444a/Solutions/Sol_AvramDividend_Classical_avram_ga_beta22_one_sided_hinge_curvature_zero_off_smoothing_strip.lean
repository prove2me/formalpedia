-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_beta22_one_sided_hinge_curvature_zero_off_smoothing_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T23:35:00.179603+00:00
-- url     : https://prove2.me/submissions/2641497e-2097-4a21-acf2-825b0812135f

import Mathlib
open Set Filter Topology
noncomputable section

theorem solution
    (b ε y : ℝ) (hε : 0 < ε)
    (hy : y < b ∨ b + ε < y) :
    iteratedDeriv 2 (fun z : ℝ => if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2) y = 0 := by
  let Q : ℝ → ℝ := fun z =>
    if z ≤ b then (0 : ℝ) else if z ≤ b + ε then
      (1 / ε ^ 2) * (z - b) ^ 3 - (1 / (2 * ε ^ 3)) * (z - b) ^ 4
    else z - b - ε / 2
  change iteratedDeriv 2 Q y = 0
  rcases hy with hlo | hhi
  · have hd : deriv Q =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds hlo] with t ht
      change t < b at ht
      have he : Q =ᶠ[𝓝 t] (fun _ : ℝ => 0) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with u hu
        change u < b at hu
        simp [Q, le_of_lt hu]
      rw [he.deriv_eq, deriv_const]
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, deriv_const]
  · have hd : deriv Q =ᶠ[𝓝 y] (fun _ : ℝ => 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds hhi] with t ht
      change b + ε < t at ht
      have he : Q =ᶠ[𝓝 t] (fun u : ℝ => u - b - ε / 2) := by
        filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
        change b + ε < u at hu
        have hb : b < u := by linarith
        simp [Q, not_le.mpr hb, not_le.mpr hu]
      rw [he.deriv_eq]
      simp only [deriv_sub_const]
      change deriv id t = 1
      exact (hasDerivAt_id t).deriv
    rw [show (2 : ℕ) = 1 + 1 by norm_num,
      iteratedDeriv_succ, iteratedDeriv_one, hd.deriv_eq, deriv_const]
