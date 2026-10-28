-- Prove2me | solution 1 for AvramDividend.Classical.levy_upperExit_noLowerCrossing_horizon_filtration_measurable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:00:02.079297+00:00
-- url     : https://prove2.me/submissions/7f75bc96-4fb8-49e1-913b-9177a7753c77

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
    (upper lower : ℝ) (T : ℝ≥0) :
    MeasurableSet[𝓕 T]
      {ω : Ω |
        (⨅ (t : ℝ≥0) (_ : upper < X.X t ω), (t : ℝ≥0∞)) <
          (T : ℝ≥0∞) ∧
        ¬ ∃ s : ℝ≥0, s < T ∧ X.X s ω < lower} :=
  (AvramDividend.Classical.levy_upperPassage_lt_filtration_measurable X upper T).inter
    (AvramDividend.Classical.levy_lowerCrossing_before_filtration_measurable X lower T).compl
