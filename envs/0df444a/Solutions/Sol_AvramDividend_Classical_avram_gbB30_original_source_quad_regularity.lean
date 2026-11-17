-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_original_source_quad_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:41:19.34964+00:00
-- url     : https://prove2.me/submissions/86b6005b-f928-4e9e-a871-aa67d5207a65

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB30_piecewise_quadratic_cap_smoothness
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution :
    0 ≤ (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) 0 ∧
      ContinuousOn (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) (Ici 0) ∧
      (∀ y : ℝ, y < 0 → (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2) y = 0) ∧
      ContDiffOn ℝ 2 (fun u : ℝ => if u < 0 then 0 else 2 * u - 4 * u ^ 2)
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y <
          ENNReal.ofReal (1 / 8 : ℝ)} := by 
  obtain ⟨hcont, hC2, hzero, hneg⟩ :=
    avram_gbB30_piecewise_quadratic_cap_smoothness
  refine ⟨by exact le_of_eq hzero.symm, hcont, hneg, ?_⟩
  apply hC2.mono
  intro y hy
  refine ⟨hy.1, ?_⟩
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (le_of_lt hy.1)).mp hy.2
