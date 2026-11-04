-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_strict_grid_sum_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:14:37.438141+00:00
-- url     : https://prove2.me/submissions/3a6089a0-176e-4c8a-8def-c7e0fdf3694c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The finite original-process negative-grid indicator count is measurable. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Measurable (fun ω : Ω =>
      ∑ i ∈ Finset.range (n + 1),
        (if X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
            X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2
          then (1 : ℝ≥0∞) else 0)) := by
  have hfuture :=
    avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X 0
  have hcoord (t : ℝ≥0) :
      Measurable (fun ω : Ω => X.X t ω - X.X 0 ω) := by
    simpa only [zero_add, Function.comp_def] using (measurable_pi_apply t).comp hfuture
  have hcell (i : ℕ) :
      Measurable (fun ω : Ω =>
        X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
        X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) := by
    have h := (hcoord (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).sub
      (hcoord ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
    convert h using 1
    funext ω
    dsimp
    ring
  apply Finset.measurable_sum
  intro i hi
  have hs : MeasurableSet {ω : Ω |
      X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
        X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω < -ε / 2} :=
    measurableSet_Iio.preimage (hcell i)
  exact Measurable.ite hs measurable_const measurable_const
