-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_actual_original_grid_mean_horizon_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:21:11.318844+00:00
-- url     : https://prove2.me/submissions/7beb8463-132d-453f-9343-bc4b41279563

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_uniform_real_rate_mesh_sum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original Lévy source has a horizon-uniform bound on grid means. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop,
        (∫⁻ ω, ∑ i ∈ Finset.range (n + 1),
          (Iic (-ε)).indicator (fun _ : ℝ => (1 : ℝ≥0∞))
            (X.X (((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω -
              X.X ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))) ω) ∂P) ≤
        ENNReal.ofReal (C * (T : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_p2_34dbea70_actual_original_negative_grid_mean_uniform_tail_bound
      X T hT ε hε
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound] with n hn
  simpa only [avram_p2_34dbea70_uniform_real_rate_mesh_sum T C (le_of_lt hC) n]
    using hn
