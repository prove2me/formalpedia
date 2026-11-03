-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_cadlag_marked_grid_correctness_gives_product_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:40:30.478402+00:00
-- url     : https://prove2.me/submissions/d463c4c0-b0dd-49ea-95ec-5c6f9d348f62

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_sup_product_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- A correct càdlàg grid limit is automatically product-measurable. -/
theorem solution
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by
  refine ⟨(fun Y => (⨆ k : ℕ, (((Finset.range (n k)).filter (fun i =>
          Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))), ?_, ?_⟩
  · exact avram_wave7_01_countable_marked_grid_sup_product_measurable
      B hB n grid
  · intro Y hRight hLeft
    exact hGrid Y hRight hLeft
