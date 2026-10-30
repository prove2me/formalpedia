-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_lower_clock_strict_preclock_closed_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:40:34.799287+00:00
-- url     : https://prove2.me/submissions/a014a137-1055-4a17-8267-b53fbfda0e05

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A strict pre-ruin clock preserves true closed past-history nonnegative reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω := by
  intro s hst
  by_contra hneg
  have hbelow : X.X s ω < -x := by linarith
  have hclock : twoSidedExitDownTime X (-x) ω ≤ (s : ℝ≥0∞) := by
    change (⨅ (u : ℝ≥0) (_ : X.X u ω < -x),
      (u : ℝ≥0∞)) ≤ (s : ℝ≥0∞)
    exact iInf_le_of_le s (iInf_le _ hbelow)
  have hle : (s : ℝ≥0∞) ≤ (t : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hst
  exact (not_le_of_gt ht) (hclock.trans hle)
