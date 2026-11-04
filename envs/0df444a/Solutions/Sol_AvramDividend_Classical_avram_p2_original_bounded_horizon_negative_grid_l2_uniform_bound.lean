-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:58:15.500205+00:00
-- url     : https://prove2.me/submissions/ec98c7db-925a-42d0-8c4b-e082f54fb333

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_uniform_negative_grid_probability_mass
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_equispaced_negative_grid_quadratic_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Original source negative-increment grid counts have uniformly bounded
second moments at bounded horizon and vanishing positive mesh. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
        (∫⁻ ω, (∑ i ∈ Finset.range n,
          ({v : Ω | X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) v -
              X.X ((i : ℝ≥0) * Real.toNNReal h) v ≤ -ε}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
          ENNReal.ofReal (C * T) + (ENNReal.ofReal (C * T)) ^ 2 := by
  obtain ⟨C, hC, hRate⟩ :=
    avram_p2_original_uniform_negative_grid_probability_mass X ε hε T hT
  refine ⟨C, hC, ?_⟩
  filter_upwards [hRate] with h hBound
  intro n hn
  have hMass := hBound n hn
  have hBase :=
    avram_p2_original_equispaced_negative_grid_quadratic_bound
      X (Real.toNNReal h) n ε
  calc
    (∫⁻ ω, (∑ i ∈ Finset.range n,
      ({v : Ω | X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) v -
          X.X ((i : ℝ≥0) * Real.toNNReal h) v ≤ -ε}).indicator
        (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
      (n : ℝ≥0∞) * P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε} +
        ((n : ℝ≥0∞) * P {ω : Ω | X.X (Real.toNNReal h) ω ≤ -ε}) ^ 2 := hBase
    _ ≤ ENNReal.ofReal (C * T) + (ENNReal.ofReal (C * T)) ^ 2 := by
      gcongr <;> exact hMass
