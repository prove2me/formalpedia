-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_local_left_grid_samples_recover_left_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:11:35.005675+00:00
-- url     : https://prove2.me/submissions/39175435-2650-49c7-a090-d03c77c3ea3a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The left limit is recovered using bounds for this path alone. -/
theorem solution
    (grid : ℕ → ℝ≥0) (Y : ℝ≥0 → ℝ) (τ : ℝ≥0)
    (lower : ℕ → ℝ≥0) (index : ℕ → ℕ)
    (hBounds : ∀ n : ℕ, lower n ≤ grid (index n) ∧
      grid (index n) < τ)
    (hLower : Tendsto lower atTop (𝓝 τ))
    (hLeft : Tendsto Y (𝓝[<] τ) (𝓝 (Function.leftLim Y τ))) :
    Tendsto (fun n : ℕ => Y (grid (index n)))
      atTop (𝓝 (Function.leftLim Y τ)) := by
  have hConst : Tendsto (fun _ : ℕ => τ) atTop (𝓝 τ) :=
    tendsto_const_nhds
  have hGrid : Tendsto (fun n : ℕ => grid (index n))
      atTop (𝓝 τ) :=
    Filter.Tendsto.squeeze hLower hConst
      (fun n => (hBounds n).1)
      (fun n => le_of_lt (hBounds n).2)
  have hWithin : Tendsto (fun n : ℕ => grid (index n))
      atTop (𝓝[<] τ) := by
    apply (tendsto_nhdsWithin_iff).2
    exact ⟨hGrid, Filter.Eventually.of_forall
      (fun n => (hBounds n).2)⟩
  exact Filter.Tendsto.comp hLeft hWithin
