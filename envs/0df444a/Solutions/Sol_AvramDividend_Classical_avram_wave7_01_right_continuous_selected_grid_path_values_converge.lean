-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_right_continuous_selected_grid_path_values_converge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:03:12.324541+00:00
-- url     : https://prove2.me/submissions/085f91bd-cb4d-4c46-8ece-7076f87a8335

import Mathlib
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Shrinking grid samples from the right recover a right-continuous path value. -/
theorem solution
    (grid : ℕ → ℝ≥0) (t : (ℝ≥0 → ℝ) → ℝ≥0)
    (ε : ℕ → ℝ≥0) (hε : Tendsto ε atTop (𝓝 0))
    (index : ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hBounds : ∀ (Y : ℝ≥0 → ℝ) (n : ℕ),
      t Y ≤ grid (index n Y) ∧
      grid (index n Y) ≤ t Y + ε n) :
    ∀ Y : ℝ≥0 → ℝ,
      ContinuousWithinAt Y (Ici (t Y)) (t Y) →
      Tendsto (fun n : ℕ => Y (grid (index n Y)))
        atTop (𝓝 (Y (t Y))) := by
  intro Y hRight
  have hConst : Tendsto (fun _ : ℕ => t Y) atTop (𝓝 (t Y)) :=
    tendsto_const_nhds
  have hUpper : Tendsto (fun n : ℕ => t Y + ε n)
      atTop (𝓝 (t Y)) := by
    have hAdd : Tendsto (fun n : ℕ => t Y + ε n)
        atTop (𝓝 (t Y + 0)) := hConst.add hε
    simpa only [add_zero] using hAdd
  have hGrid : Tendsto (fun n : ℕ => grid (index n Y))
      atTop (𝓝 (t Y)) :=
    Filter.Tendsto.squeeze hConst hUpper
      (fun n => (hBounds Y n).1)
      (fun n => (hBounds Y n).2)
  have hWithin : Tendsto (fun n : ℕ => grid (index n Y))
      atTop (𝓝[Ici (t Y)] (t Y)) := by
    apply (tendsto_nhdsWithin_iff).2
    exact ⟨hGrid, Filter.Eventually.of_forall
      (fun n => (hBounds Y n).1)⟩
  exact Filter.Tendsto.comp hRight hWithin
