-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01b_true_surviving_horizon_reserve_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T13:53:58.479077+00:00
-- url     : https://prove2.me/submissions/dd76bc04-214d-486d-ae1a-faffc65ddc0d

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_le_observation_of_strict_exceedance
import Theorems.Thm_AvramDividend_Classical_twoSidedExitDownTime_le_of_strict_lower_gap_observed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Before both original stopping clocks, all observed reserves stay in the closed strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x : ℝ)
    (T : ℝ≥0) (ω : Ω)
    (hTU : (T : ℝ≥0∞) < twoSidedExitUpTime X (a-x) ω)
    (hTD : (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω) :
    ∀ s : ℝ≥0, s ≤ T →
      0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a := by
  intro s hs
  have hst : (s : ℝ≥0∞) ≤ (T : ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr hs
  have hu : X.X s ω ≤ a-x := by
    by_contra hn
    have hbad : a-x < X.X s ω := lt_of_not_ge hn
    have hhit := twoSidedExitUpTime_le_observation_of_strict_exceedance
      X a x ω s hbad
    exact (not_lt_of_ge hhit) (lt_of_le_of_lt hst hTU)
  have hl : -x ≤ X.X s ω := by
    by_contra hn
    have hbad : X.X s ω < -x := lt_of_not_ge hn
    have hhit := twoSidedExitDownTime_le_of_strict_lower_gap_observed
      X x ω s hbad
    exact (not_lt_of_ge hhit) (lt_of_le_of_lt hst hTD)
  constructor <;> linarith
