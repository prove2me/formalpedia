-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_shifted_future_increment_independent_of_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:44:08.477742+00:00
-- url     : https://prove2.me/submissions/b9937d8b-3b10-4550-b006-b5167d319842

import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- The exact original future increment is independent of the original past filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) :
    Indep
      (MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
      (𝓕 s) P := by
  exact X.indepIncrements s (s + t) (by simp)
