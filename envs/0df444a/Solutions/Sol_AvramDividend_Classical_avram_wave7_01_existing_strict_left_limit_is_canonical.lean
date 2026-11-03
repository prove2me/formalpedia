-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_existing_strict_left_limit_is_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:17:02.615095+00:00
-- url     : https://prove2.me/submissions/6e1a9a3d-d681-4f32-b48d-95516fab8fec

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- An existing finite strict-left limit at positive time coincides with leftLim. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (hu : 0 < u)
    (hLeft : ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by
  obtain ⟨l, hl⟩ := hLeft
  haveI : (𝓝[<] u).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  have heq : Function.leftLim Y u = l := leftLim_eq_of_tendsto hl
  simpa only [heq] using hl
