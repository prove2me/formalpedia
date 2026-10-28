-- Prove2me | solution 1 for AvramDividend.Classical.chat08_deterministic_levy_increment_regeneration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:52:09.772506+00:00
-- url     : https://prove2.me/submissions/6c73ecb2-5bb8-451a-8af2-69bd085b66b3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-! Deterministic Lévy increments regenerate in distribution and are independent of the past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (s u : ℝ≥0) :
    IdentDistrib
        (fun ω => X.X (s + u) ω - X.X s ω) (X.X u) P P ∧
      Indep
        (MeasurableSpace.comap
          (fun ω => X.X (s + u) ω - X.X s ω) inferInstance)
        (ℱ s) P := by
  constructor
  · have hdist := X.stationaryIncrements s (s + u)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from zero_le))
    simpa only [add_tsub_cancel_left] using hdist
  · exact X.indepIncrements s (s + u)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from zero_le))
