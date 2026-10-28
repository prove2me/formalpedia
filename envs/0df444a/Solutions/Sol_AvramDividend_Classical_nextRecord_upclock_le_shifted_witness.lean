-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_upclock_le_shifted_witness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:51:01.55408+00:00
-- url     : https://prove2.me/submissions/7a4026e4-20f3-4928-a3e2-341547fd2db2

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Transfer a future shifted upper crossing into the original named clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (u t : ℝ≥0) (ω : Ω)
    (hAt : X.X u ω = b)
    (hNext : ε < X.X (u + t) ω - X.X u ω) :
    twoSidedExitUpTime X (b + ε) ω ≤ ((u + t : ℝ≥0) : ℝ≥0∞) := by
  have hCross : b + ε < X.X (u + t) ω := by
    linarith
  change (⨅ (s : ℝ≥0) (_ : b + ε < X.X s ω),
    (s : ℝ≥0∞)) ≤ ((u + t : ℝ≥0) : ℝ≥0∞)
  exact iInf_le_of_le (u + t) (iInf_le_of_le hCross le_rfl)
