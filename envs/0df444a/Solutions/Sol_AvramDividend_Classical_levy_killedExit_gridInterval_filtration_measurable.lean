-- Prove2me | solution 1 for AvramDividend.Classical.levy_killedExit_gridInterval_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:05:10.438594+00:00
-- url     : https://prove2.me/submissions/26c65da4-bf03-48ca-8405-8c57b694ae44

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upperPassage_lt_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_levy_lowerCrossing_before_filtration_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper lower : ℝ) (S T : ℝ≥0) (hST : S ≤ T) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (T : ℝ≥0∞) ∧
        ¬ (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) < (S : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} :=
  (AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable X upper T).inter
    ((𝓕.mono hST _
      (AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable X upper S)).compl.inter
    (AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable X lower T).compl)
