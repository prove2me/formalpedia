-- Prove2me | solution 1 for AvramDividend.Classical.levyPath_bddAbove_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:18:12.823273+00:00
-- url     : https://prove2.me/submissions/eca2c983-3459-4e1c-b17e-f1eab617590f

import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every finite Levy path interval is bounded above by its terminal running record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 T) := by
  obtain ⟨hmono, hdom⟩ := runningSup_monotone_and_path_le X ω
  refine ⟨runningSup X T ω, ?_⟩
  rintro y ⟨r, hr, rfl⟩
  exact (hdom r).trans (hmono hr.2)
