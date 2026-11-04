-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_separated_band_weight_controls_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:39:54.810684+00:00
-- url     : https://prove2.me/submissions/4d63be82-9f8e-4944-a364-bf10d9ec1a4d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) :
    0 < (1 - Real.exp (-θ * ε)) ^ 4 ∧
      ∀ y : ℝ,
        (1 - Real.exp (-θ * ε)) ^ 4 *
          (if y ≤ -ε then (1 : ℝ) else 0) ≤
        (Real.exp (θ * y) - 1) ^ 4 := by
  have hmul : -θ * ε < 0 := by
    nlinarith [mul_pos hθ hε]
  have he : Real.exp (-θ * ε) < 1 := by
    have h := Real.exp_lt_exp.mpr hmul
    simpa using h
  have hk : 0 < 1 - Real.exp (-θ * ε) := by linarith
  refine ⟨pow_pos hk 4, ?_⟩
  intro y
  by_cases hy : y ≤ -ε
  · simp only [hy, ↓reduceIte, mul_one]
    have hm : θ * y ≤ -θ * ε := by
      have hz := mul_le_mul_of_nonneg_left hy hθ.le
      nlinarith
    have hx : Real.exp (θ * y) ≤ Real.exp (-θ * ε) :=
      Real.exp_le_exp.mpr hm
    calc
      (1 - Real.exp (-θ * ε)) ^ 4 ≤
          (1 - Real.exp (θ * y)) ^ 4 := by
            gcongr
      _ = (Real.exp (θ * y) - 1) ^ 4 := by ring
  · simp only [hy, ↓reduceIte, mul_zero]
    positivity
