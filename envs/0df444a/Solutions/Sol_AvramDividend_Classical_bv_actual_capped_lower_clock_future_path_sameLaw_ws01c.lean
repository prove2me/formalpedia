-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_capped_lower_clock_future_path_sameLaw_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T07:51:40.037998+00:00
-- url     : https://prove2.me/submissions/f0b91e09-2c00-447d-85c1-f30d0f1e80ea

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_finite_capped_grid_right_clock_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_raw_lower_clock_NNReal_measurable_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_grid_stop_limit_full_future_path_law_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0)
    (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
      X.X ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal + t) ω -
      X.X ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal) ω) P =
    Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P := by
  let grid : ℕ → Ω → ℝ≥0 := fun n ω =>
    bv_finite_grid_below_NNReal_ws01c
      X.X lower ((M n : ℝ≥0) * mesh n)
      ((List.range (M n + 1)).map
        (fun k : ℕ => (k : ℝ≥0) * mesh n)) ω ⊓ T
  let raw : Ω → ℝ≥0 := fun ω =>
    (twoSidedExitDownTime X lower ω ⊓
      (T : ℝ≥0∞)).toNNReal
  obtain ⟨hStop, hConverges, hAbove⟩ :=
    bv_actual_finite_capped_grid_right_clock_ws01c
      X lower T mesh M hpos hzero hCover
  have hRawMeas : Measurable raw :=
    bv_capped_raw_lower_clock_NNReal_measurable_ws01c X lower T
  exact bv_grid_stop_limit_full_future_path_law_ws01c
    X grid raw hConverges hAbove hStop hRawMeas