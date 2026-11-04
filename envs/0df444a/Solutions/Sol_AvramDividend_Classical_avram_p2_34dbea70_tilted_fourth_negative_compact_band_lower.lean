-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_tilted_fourth_negative_compact_band_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:21:50.171422+00:00
-- url     : https://prove2.me/submissions/b6ef7ef1-81e6-4a24-8d54-4a0855f83432

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- A positive exponential tilt preserves a fixed lower bound on a negative jump band. -/
theorem solution (ρ θ ε M y : ℝ)
    (hρ : 0 ≤ ρ) (hθ : 0 < θ) (hε : 0 < ε)
    (hlo : -M ≤ y) (hhi : y ≤ -ε) :
    Real.exp (-ρ * M) * (1 - Real.exp (-θ * ε)) ^ 4 ≤
      Real.exp (ρ * y) * (Real.exp (θ * y) - 1) ^ 4 := by
  have hρy : -ρ * M ≤ ρ * y := by
    have h := mul_le_mul_of_nonneg_left hlo hρ
    nlinarith [h]
  have hexp : Real.exp (-ρ * M) ≤ Real.exp (ρ * y) :=
    Real.exp_le_exp.mpr hρy
  have hweight :
      (1 - Real.exp (-θ * ε)) ^ 4 ≤
        (Real.exp (θ * y) - 1) ^ 4 :=
    avram_p2_34dbea70_fourth_exponential_negative_band_uniform_lower
      θ ε y hθ hε hhi
  have hnonneg : 0 ≤ (1 - Real.exp (-θ * ε)) ^ 4 := by positivity
  have hexpnonneg : 0 ≤ Real.exp (ρ * y) := le_of_lt (Real.exp_pos _)
  exact mul_le_mul hexp hweight hnonneg hexpnonneg
