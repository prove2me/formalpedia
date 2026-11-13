-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_finite_borel_rate_square_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T13:51:28.006937+00:00
-- url     : https://prove2.me/submissions/8cee4946-837a-4f00-a495-cd7183057b16

import Mathlib

open MeasureTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

set_option autoImplicit false

/-- For a finite measure value, the real-valued square rate agrees with the `ℝ≥0∞` computation. -/
theorem solution (μ : Measure ℝ) (B : Set ℝ) (T : ℝ≥0) (hν : μ B < ⊤) :
    ENNReal.ofReal ((((T : ℝ) * (μ B).toReal) ^ 2) / 2) =
      (((T : ℝ≥0∞) * μ B) ^ 2) / 2 := by
  have hμ : μ B ≠ ⊤ := ne_of_lt hν
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (T : ℝ) * (μ B).toReal)]
  rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (T : ℝ))]
  rw [ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_toReal hμ]
  rw [ENNReal.ofReal_ofNat]
