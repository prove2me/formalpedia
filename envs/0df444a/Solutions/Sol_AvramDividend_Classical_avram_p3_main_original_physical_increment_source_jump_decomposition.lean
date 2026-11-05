-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_physical_increment_source_jump_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:27:29.0771+00:00
-- url     : https://prove2.me/submissions/c2c217a3-cfab-448f-b3dc-605ee39e6979

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Exact same-source physical increment equals the jump-removed BV increment
minus actual intrinsic left-jump masses, without a zero-residual assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) :
    let J : ℝ≥0 → ℝ := fun t =>
      (∑' s : ℝ≥0, if 0 < s ∧ s ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) s - X.X s ω
      else 0)
    (X.X v ω - X.X u ω) =
      ((X.X v ω + J v) - (X.X u ω + J u)) -
        (J v - J u) := by
  intro J
  ring
