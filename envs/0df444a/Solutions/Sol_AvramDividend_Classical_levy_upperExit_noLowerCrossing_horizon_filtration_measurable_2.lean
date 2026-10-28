-- Prove2me | solution 2 for AvramDividend.Classical.levy_upperExit_noLowerCrossing_horizon_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:00:12.963737+00:00
-- url     : https://prove2.me/submissions/2132a422-826b-4479-867f-eaa6da0e36b1

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strict upper exit before a horizon with no prior lower crossing is past-observable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  have hu := levy_upperPassage_lt_filtration_measurable X upper T
  have hl := levy_lowerCrossing_before_filtration_measurable X lower T
  exact hu.inter hl.compl
