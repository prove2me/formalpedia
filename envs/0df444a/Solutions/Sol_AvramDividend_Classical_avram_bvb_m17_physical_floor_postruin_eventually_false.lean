-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_m17_physical_floor_postruin_eventually_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:31:55.036903+00:00
-- url     : https://prove2.me/submissions/03d0e02c-83b8-4b9c-ac70-f65c76744c46

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_m17_uniform_floor_original_grid_eq
import Theorems.Thm_AvramDividend_Classical_avram_bva20_postruin_uniform_floor_mask_eventually_false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (r : ℝ) (hr : 0 < r) (τ : ℝ≥0∞)
    (hτ : τ < (Real.toNNReal r : ℝ≥0∞)) :
    ∀ᶠ n in Filter.atTop,
      ¬ ((u n ⌊(r / T) * ((n : ℝ) + 2)⌋₊ : ℝ≥0∞) < τ) := by
  have hrcoe : (Real.toNNReal r : ℝ) = r :=
    Real.coe_toNNReal r hr.le
  have hbase :=
    avram_bva20_postruin_uniform_floor_mask_eventually_false
      T hT (Real.toNNReal r) τ hτ
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hbase] with n hn
  rw [avram_bvb_m17_uniform_floor_original_grid_eq T hT u huniform n r]
  simpa only [hrcoe] using hn
