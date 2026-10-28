-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_crossing_after_firstRecord
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:02:44.937573+00:00
-- url     : https://prove2.me/submissions/46353afe-640a-4c50-8cc9-5b05eafbbc79

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

 /-! A later higher crossing is a genuine shifted future crossing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u t : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b)
    (hNext : b + ε < X.X t ω) :
    u ≤ t ∧ ε < X.X t ω - X.X u ω := by
  have hBase : b < X.X t ω := by
    linarith
  have hClock : twoSidedExitUpTime X b ω ≤ (t : ℝ≥0∞) := by
    change (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)) ≤ (t : ℝ≥0∞)
    exact iInf_le_of_le t (iInf_le_of_le hBase le_rfl)
  have hTime : u ≤ t := by
    rw [← hu] at hClock
    exact ENNReal.coe_le_coe.mp hClock
  constructor
  · exact hTime
  · rw [hAt]
    linarith
