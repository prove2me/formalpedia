-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_cadlag_marked_liminf_correctness_gives_product_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:06:30.420807+00:00
-- url     : https://prove2.me/submissions/a45c3fe6-49f0-458f-88e7-1a98bc8b5e1f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- A correct marked-grid lower-tail limit is a measurable path extractor. -/
theorem solution
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (n : ℕ → ℕ) (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ Y : ℝ≥0 → ℝ,
      (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
      (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
      ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = (⨆ m : ℕ, ⨅ k : ℕ, if m ≤ k then
          ((((Finset.range (n k)).filter (fun i =>
            Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))
          else ⊤)) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u → ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) →
        ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
          Y v - Function.leftLim Y v ≠ 0 ∧
          Y v - Function.leftLim Y v ∈ B}).encard = F Y := by
  refine ⟨(fun Y => (⨆ m : ℕ, ⨅ k : ℕ, if m ≤ k then
          ((((Finset.range (n k)).filter (fun i =>
            Y (grid k (i + 1)) - Y (grid k i) ∈ B)).card : ℝ≥0∞))
          else ⊤)), ?_, ?_⟩
  · exact avram_wave7_01_countable_marked_grid_lower_tail_envelope_measurable
      B hB n grid
  · intro Y hRight hLeft
    exact hGrid Y hRight hLeft
