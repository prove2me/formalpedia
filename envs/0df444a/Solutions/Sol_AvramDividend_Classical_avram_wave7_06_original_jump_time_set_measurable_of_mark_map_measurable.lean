-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_jump_time_set_measurable_of_mark_map_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:12:26.905328+00:00
-- url     : https://prove2.me/submissions/4851fbb9-9c7e-47aa-bedd-636b1971c6f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Borel measurability of genuine X jump times from the original mark map. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMark : Measurable
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) :
    MeasurableSet {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
  have hDiff : Measurable (fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
    measurable_snd.comp hMark
  have hNonzero : MeasurableSet {u : ℝ≥0 |
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} := by
    change MeasurableSet ((fun u : ℝ≥0 =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ⁻¹'
      ({0}ᶜ : Set ℝ))
    exact hDiff ((measurableSet_singleton (0 : ℝ)).compl)
  exact measurableSet_Ioi.inter hNonzero
