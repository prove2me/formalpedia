-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_uniform_cell_increment_to_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:12:02.123602+00:00
-- url     : https://prove2.me/submissions/3286caa7-b617-4914-affb-d08a5761e657

import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_source_jump_cells_sided_limits

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Topology AvramDividend.Classical
open scoped NNReal

/-- An original uniform-grid cell containing a jump has increment tending to its exact mark. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T u : ℝ≥0)
    (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (hL : Tendsto Y (nhdsWithin u (Iio u))
      (𝓝 (Function.leftLim Y u)))
    (hR : ContinuousWithinAt Y (Ici u) u) :
    ∃ i : ℕ → ℕ,
      (∀ n, i n ≤ n ∧
        (i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
        u ≤ ((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ∧
      Tendsto (fun n =>
        Y (((i n + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) -
          Y ((i n : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
        atTop (𝓝 (Y u - Function.leftLim Y u)) := by
  obtain ⟨i, hcell, hleft, hright⟩ :=
    avram_p2_34dbea70_uniform_source_jump_cells_sided_limits T u hT hu huT
  refine ⟨i, hcell, ?_⟩
  exact (hR.tendsto.comp hright).sub (hL.comp hleft)
