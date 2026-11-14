-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T14:53:10.679543+00:00
-- url     : https://prove2.me/submissions/64501a0d-8847-4284-8e46-2476e57f7bc9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original signed source jump and leftjump magnitude series are pointwise opposites. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0) =
    -(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω else 0) := by
  calc
    _ = ∑' u : ℝ≥0, -(if 0 < u ∧ u ≤ t then
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω else 0) := by
          apply tsum_congr
          intro u
          by_cases hu : 0 < u ∧ u ≤ t <;> simp [hu] <;> ring
    _ = _ := tsum_neg
