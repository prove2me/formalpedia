-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_grid_count_quadratic_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:47:10.183916+00:00
-- url     : https://prove2.me/submissions/282ce40a-36b8-4f4e-8a6e-428deecd9bdb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_grid_count_exact_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Actual source-past conditional quadratic bound on finite marked increment grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (hst : s ≤ t 0)
    (n : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω,
      (A.indicator (fun _ => (1 : ℝ≥0∞)) ω) *
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
    P A * ((∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) +
      (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) ^ 2) := by
  classical
  calc
    _ = P A * (∫⁻ ω,
      (∑ i ∈ Finset.range n,
        ({v : Ω | X.X (t (i + 1)) v - X.X (t i) v ∈ B}).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) :=
      avram_wave6_01_original_past_marked_grid_count_exact_second_moment
        X s t ht hst n A hA B hB
    _ ≤ P A * ((∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) +
      (∑ i ∈ Finset.range n,
      P {ω | X.X (t (i + 1)) ω - X.X (t i) ω ∈ B}) ^ 2) := by
      gcongr
      exact avram_wave6_01_original_borel_marked_grid_count_second_moment_upper_bound
        X t ht n B hB
