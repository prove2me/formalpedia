-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_liminf_horizon_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:38:00.438212+00:00
-- url     : https://prove2.me/submissions/5a704fd5-b27a-4241-adc3-9794f4ef93d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original grid expectation has a finite liminf independent of n. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      Filter.liminf (fun n : ℕ =>
        ∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) atTop ≤
        ENNReal.ofReal (C * (T : ℝ)) := by
  obtain ⟨C, hC, hevent⟩ :=
    avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform
      X T hT ε hε
  refine ⟨C, hC, ?_⟩
  calc
    _ ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal (C * (T : ℝ))) atTop :=
      Filter.liminf_le_liminf hevent
    _ = _ := by simp
