-- Prove2me | solution 1 for DQI.Semicircle.eq_137
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:51:46.013457+00:00
-- url     : https://prove2.me/submissions/0484d2c5-1c5e-4686-abaf-2933def8f68c

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting

theorem solution (ρ μ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ρ + Real.sqrt (ρ * (1 - ρ)) *
        (μ * ((1 - 2 * ρ) / Real.sqrt (ρ * (1 - ρ))) + 2 * Real.sqrt (μ * (1 - μ))) =
      (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2 := by
  have h1 : 0 < ρ * (1 - ρ) := mul_pos hρ0 (by linarith)
  have hs : 0 < Real.sqrt (ρ * (1 - ρ)) := Real.sqrt_pos.mpr h1
  have a1 : 0 ≤ μ * (1 - ρ) := mul_nonneg hμ0 (by linarith)
  have a2 : 0 ≤ ρ * (1 - μ) := mul_nonneg hρ0.le (by linarith)
  have a3 : 0 ≤ μ * (1 - μ) := mul_nonneg hμ0 (by linarith)
  have hc : Real.sqrt (ρ * (1 - ρ)) * Real.sqrt (μ * (1 - μ)) =
      Real.sqrt (μ * (1 - ρ)) * Real.sqrt (ρ * (1 - μ)) := by
    rw [← Real.sqrt_mul h1.le, ← Real.sqrt_mul a1]
    congr 1
    ring
  have hd : Real.sqrt (ρ * (1 - ρ)) * (μ * ((1 - 2 * ρ) / Real.sqrt (ρ * (1 - ρ)))) =
      μ * (1 - 2 * ρ) := by
    field_simp
  rw [mul_add, hd, add_sq, Real.sq_sqrt a1, Real.sq_sqrt a2]
  have : Real.sqrt (ρ * (1 - ρ)) * (2 * Real.sqrt (μ * (1 - μ))) =
      2 * (Real.sqrt (μ * (1 - ρ)) * Real.sqrt (ρ * (1 - μ))) := by
    rw [← hc]; ring
  rw [this]
  ring
