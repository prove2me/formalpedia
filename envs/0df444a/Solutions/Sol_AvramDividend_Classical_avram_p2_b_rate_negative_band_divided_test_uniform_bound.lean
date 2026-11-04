-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_negative_band_divided_test_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:32:58.678906+00:00
-- url     : https://prove2.me/submissions/24910c05-b644-41e4-af71-e5a9c630a600

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_fourth_weight_lower
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_negative_band_weight_constant_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

theorem solution
    (θ ε M : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (hM : 0 ≤ M)
    (f : ℝ → ℝ) (hf : ∀ y : ℝ, y ≤ -ε → |f y| ≤ M)
    (y : ℝ) (hy : y ≤ -ε) :
    |f y / (Real.exp (θ * y) - 1) ^ 4| ≤
      M / (1 - Real.exp (-θ * ε)) ^ 4 := by
  let C : ℝ := (1 - Real.exp (-θ * ε)) ^ 4
  let W : ℝ := (Real.exp (θ * y) - 1) ^ 4
  have hC : 0 < C :=
    AvramDividend.Classical.avram_p2_b_rate_negative_band_weight_constant_pos
      θ ε hθ hε
  have hCW : C ≤ W :=
    AvramDividend.Classical.avram_p2_b_rate_negative_band_fourth_weight_lower
      θ ε y hθ hε hy
  have hW : 0 < W := lt_of_lt_of_le hC hCW
  have hmul : |f y| * C ≤ M * W := calc
    |f y| * C ≤ M * C :=
      mul_le_mul_of_nonneg_right (hf y hy) (le_of_lt hC)
    _ ≤ M * W := mul_le_mul_of_nonneg_left hCW hM
  have hdiv : |f y| / W ≤ M / C :=
    (div_le_div_iff₀ hW hC).mpr hmul
  change |f y / W| ≤ M / C
  simpa only [abs_div, abs_of_pos hW] using hdiv