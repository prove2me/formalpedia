-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_f_original_unit_grid_cell_product_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T18:52:04.245478+00:00
-- url     : https://prove2.me/submissions/37d1bc9d-6d2c-4a8e-83ef-8515a9fd70dd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_original_cell_product_laplace
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_unit_grid_cell_finset_stable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s t : ℝ≥0) (ht : t ≤ 1) (k : ℕ) :
    (∏ u ∈ (avram_redux19_original_strict_negative_marked_times_finite
      X ω (1 : ℝ≥0) k).toFinset.filter (fun u => s < u ∧ u ≤ t),
      Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) =
    Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) := by
  rw [avram_route_runner_f_original_unit_grid_cell_finset_stable X ω s t ht k]
  exact (avram_route_runner_e_original_cell_product_laplace X ω s t k).symm
