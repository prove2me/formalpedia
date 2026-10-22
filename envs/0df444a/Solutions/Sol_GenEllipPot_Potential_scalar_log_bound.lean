-- Prove2me | solution 1 for GenEllipPot.Potential.scalar_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:29:20.403796+00:00
-- url     : https://prove2.me/submissions/c765f06f-faa3-4054-b2be-f4462eb53786

import Mathlib

theorem solution (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x ≤ 2 * Real.log (1 + x) := by
  obtain ⟨h0, h1⟩ := hx
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have : x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
  have hx2 : x ≤ 2 * (x / (1 + x)) := by
    rw [mul_div_assoc', le_div_iff₀ hpos]; nlinarith
  linarith
