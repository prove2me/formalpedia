-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:11:24.763169+00:00
-- url     : https://prove2.me/submissions/f8f882fd-8d78-406d-b055-a7f0c77bea08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original-source marked uniform grid expectation has the actual
small-time negative-tail upper bound on every sufficiently fine grid. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) ≤
        ∑ _i ∈ Finset.range (n + 1),
          ENNReal.ofReal (C * ((T / ((n : ℝ≥0) + 1) : ℝ≥0) : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_p2_34dbea70_original_negative_tail_uniform_width_probability_O
      X T hT ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  rw [avram_p2_34dbea70_actual_uniform_original_grid_mean_stationary_cells
    X T n (Iic (-ε)) measurableSet_Iic]
  exact Finset.sum_le_sum (fun i _hi => by
    simpa only [Set.mem_Iic] using hn)
