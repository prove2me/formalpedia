-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_left_limit_negation_at_positive_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:38:10.472466+00:00
-- url     : https://prove2.me/submissions/8b71e323-612e-437d-84a1-1cffbb150358

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Strict-left limits commute with negation at positive nonnegative times. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (hu : 0 < u)
    (hLeft : Tendsto Y (𝓝[<] u)
      (𝓝 (Function.leftLim Y u))) :
    Function.leftLim (fun v : ℝ≥0 => -Y v) u =
      -Function.leftLim Y u := by
  haveI : (𝓝[<] u).NeBot :=
    nhdsLT_neBot_of_exists_lt ⟨0, hu⟩
  have hNeg : Tendsto (fun v : ℝ≥0 => -Y v) (𝓝[<] u)
      (𝓝 (-Function.leftLim Y u)) := hLeft.neg
  exact leftLim_eq_of_tendsto hNeg
