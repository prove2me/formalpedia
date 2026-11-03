-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_future_increment_independent_of_earlier_grid_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:44:43.563358+00:00
-- url     : https://prove2.me/submissions/8383b13d-5e0a-4b74-bc38-d2c518108a4a

import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Future source increments are independent of every earlier filtration grid cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (r s t : ℝ≥0) (hrs : r ≤ s) :
    Indep
      (MeasurableSpace.comap
        (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
      (𝓕 r) P := by
  have hSource :
      Indep
        (MeasurableSpace.comap
          (fun ω => X.X (s + t) ω - X.X s ω) inferInstance)
        (𝓕 s) P :=
    X.indepIncrements s (s + t) (by simp)
  exact ProbabilityTheory.indep_of_indep_of_le_right hSource (𝓕.mono hrs)
