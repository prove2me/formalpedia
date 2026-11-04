-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_marked_zero_horizon_empty
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:20:52.762382+00:00
-- url     : https://prove2.me/submissions/3a8b578d-d44c-4e71-b511-54e14f38aaf5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- The source jump measure vanishes pathwise on the empty time interval. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (B : Set ℝ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (0 : ℝ≥0) 0 ×ˢ B) = 0 := by
  simp
