-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_consecutive_future_increment_additivity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:54:40.085839+00:00
-- url     : https://prove2.me/submissions/c8fca31e-dba5-415b-b4bc-b065387615f2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source future increments telescope exactly across two adjacent time-grid cells. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u v : ℝ≥0) :
    X.X (s + u + v) ω - X.X s ω =
      (X.X (s + u) ω - X.X s ω) +
      (X.X (s + u + v) ω - X.X (s + u) ω) := by
  ring
