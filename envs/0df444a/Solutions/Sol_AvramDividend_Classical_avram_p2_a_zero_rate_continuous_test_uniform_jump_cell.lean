-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_continuous_test_uniform_jump_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:35:33.521244+00:00
-- url     : https://prove2.me/submissions/2894e954-7dc9-41e8-9ff3-b808891261af

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_cell_increment_to_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- Every genuine original jump admits shrinking grid cells whose continuous
test weights tend to the exact jump-mark weight. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T u : ℝ≥0)
    (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n =>
        f (Y (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))))
        atTop (𝓝 (f (Y u - Function.leftLim Y u))) := by
  obtain ⟨i, hcell, hmark⟩ :=
    avram_p2_a_zero_rate_uniform_cell_increment_to_jump
      Y T u hT hu huT hL hR
  refine ⟨i, hcell, ?_⟩
  exact hf.continuousAt.tendsto.comp hmark
