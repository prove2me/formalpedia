-- Prove2me | solution 2 for AvramDividend.Classical.levy_killedExit_gridInterval_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:05:43.490793+00:00
-- url     : https://prove2.me/submissions/aa2fc101-e1bd-4f51-8cda-d3f208c33161

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

/-- The killed upper-exit event in a finite grid interval is observable by the interval end. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper lower : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (T : ℝ≥0∞) ∧
        ¬ (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (S : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} := by
  have hT := levy_upperPassage_lt_filtration_measurable X upper T
  have hS : MeasurableSet[𝓕 T] {ω : Ω |
      (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (S : ℝ≥0∞)} :=
    𝓕.mono hST _ (levy_upperPassage_lt_filtration_measurable X upper S)
  have hLower := levy_lowerCrossing_before_filtration_measurable X lower T
  exact hT.inter (hS.compl.inter hLower.compl)
