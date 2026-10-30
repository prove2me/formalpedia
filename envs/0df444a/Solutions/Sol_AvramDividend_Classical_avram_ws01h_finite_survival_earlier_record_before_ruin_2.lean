-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01h_finite_survival_earlier_record_before_ruin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:36:30.314425+00:00
-- url     : https://prove2.me/submissions/e7506313-15ed-48a9-9c40-44997003346d

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- A genuinely observed upper passage before a non-ruin clock horizon
strictly precedes the source-defined lower first-passage infimum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (ω : Ω) (t : ℝ≥0)
    (hUpper : twoSidedExitUpTime X b ω < (t : ℝ≥0∞))
    (hSurvive : ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω) :
    twoSidedExitUpTime X b ω <
      twoSidedExitDownTime X (-x) ω := by
  have hLower : (t : ℝ≥0∞) ≤
      twoSidedExitDownTime X (-x) ω := by
    unfold twoSidedExitDownTime
    refine le_iInf fun s => ?_
    refine le_iInf fun hs => ?_
    have hts : t < s := by
      by_contra hn
      have hst : s ≤ t := le_of_not_gt hn
      have hp := hSurvive s hst
      linarith
    exact ENNReal.coe_le_coe.mpr hts.le
  exact hUpper.trans_le hLower
