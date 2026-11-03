-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_countable_future_marked_grid_sup_past_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:02:27.884894+00:00
-- url     : https://prove2.me/submissions/feb9da08-cfae-454d-ab1b-df56fc534fdf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_sup_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- Countably many original-source marked future grids factor from the adapted past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) (H : Ω → ℝ≥0∞)
    (hH : Measurable[𝓕 s] H)
    (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0) :
    (∫⁻ ω, H ω * (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
      (X.X (s + grid k (i + 1)) ω - X.X s ω) -
      (X.X (s + grid k i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞)) ∂P) =
      (∫⁻ ω, H ω ∂P) *
      (∫⁻ ω, (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
      (X.X (s + grid k (i + 1)) ω - X.X s ω) -
      (X.X (s + grid k i) ω - X.X s ω) ∈ B)).card : ℝ≥0∞)) ∂P) := by
  classical
  let Fpath : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun Y =>
    ⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
      Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞)
  have hF : Measurable Fpath :=
    avram_wave7_01_countable_marked_grid_sup_product_measurable B hB n grid
  exact avram_wave7_01_original_arbitrary_future_functional_past_weight_lintegral_factor
    X s H hH Fpath hF
