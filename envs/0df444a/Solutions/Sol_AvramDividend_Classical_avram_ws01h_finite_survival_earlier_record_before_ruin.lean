-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_finite_survival_earlier_record_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:36:29.306524+00:00
-- url     : https://prove2.me/submissions/96d61280-1ed8-4d86-99d0-e17371884c36

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (ω : Ω) (t : ℝ≥0)
    (hUpper : twoSidedExitUpTime X b ω < (t : ℝ≥0∞))
    (hSurvive : ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) :
    twoSidedExitUpTime X b ω <
      twoSidedExitDownTime X (-x) ω := by
  refine lt_of_lt_of_le hUpper ?_
  unfold twoSidedExitDownTime
  refine le_iInf fun s => le_iInf fun hs => ?_
  by_contra hcon
  push_neg at hcon
  have hst : s ≤ t := by
    exact_mod_cast hcon.le
  have := hSurvive s hst
  linarith
