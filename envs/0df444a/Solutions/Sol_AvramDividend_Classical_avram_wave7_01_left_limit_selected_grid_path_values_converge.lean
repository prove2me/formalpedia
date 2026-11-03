-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_left_limit_selected_grid_path_values_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:07:42.664521+00:00
-- url     : https://prove2.me/submissions/f7c873db-b831-4dce-8757-7cf20a7ceb56

import Mathlib
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Strictly left-sided adaptive grid values converge to the true left limit. -/
theorem solution
    (grid : ℕ → ℝ≥0) (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (lower : ℕ → (ℝ≥0 → ℝ) → ℝ≥0)
    (index : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      lower n Y ≤ grid (index n Y) ∧
      grid (index n Y) < t Y) :
    ∀ Y : ℝ≥0 → ℝ,
      Tendsto (fun n : ℕ => lower n Y) atTop (𝓝 (t Y)) →
      Tendsto Y (𝓝[<] (t Y)) (𝓝 (Function.leftLim Y (t Y))) →
      Tendsto (fun n : ℕ => Y (grid (index n Y)))
        atTop (𝓝 (Function.leftLim Y (t Y))) := by
  intro Y hLower hLeft
  have hConst : Tendsto (fun _ : ℕ => t Y) atTop (𝓝 (t Y)) :=
    tendsto_const_nhds
  have hGrid : Tendsto (fun n : ℕ => grid (index n Y))
      atTop (𝓝 (t Y)) :=
    Filter.Tendsto.squeeze hLower hConst
      (fun n => (hBounds Y n).1)
      (fun n => le_of_lt (hBounds Y n).2)
  have hWithin : Tendsto (fun n : ℕ => grid (index n Y))
      atTop (𝓝[<] (t Y)) := by
    apply (tendsto_nhdsWithin_iff).2
    exact ⟨hGrid, Filter.Eventually.of_forall
      (fun n => (hBounds Y n).2)⟩
  exact Filter.Tendsto.comp hLeft hWithin
