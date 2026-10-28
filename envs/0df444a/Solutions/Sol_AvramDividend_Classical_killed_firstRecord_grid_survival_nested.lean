-- Prove2me | solution 1 for AvramDividend.Classical.killed_firstRecord_grid_survival_nested
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:55:33.035978+00:00
-- url     : https://prove2.me/submissions/cfa8f727-41ff-4737-b92f-f47ff57ad651

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_threshold_iInf_mono
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Later killed records require earlier record survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a ε : ℝ) (hε : 0 ≤ ε) (n : ℕ) (ω : Ω)
    (hSurvive :
      twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω <
        barrierRuinTime X a ω) :
    twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
      barrierRuinTime X a ω := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ (n + 1)
  have hlevel :
      (((n + 1 : ℕ) : ℝ) * ε) ≤
        (((n + 2 : ℕ) : ℝ) * ε) :=
    mul_le_mul_of_nonneg_right hn hε
  have htime :
      twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω ≤
        twoSidedExitUpTime X (((n + 2 : ℕ) : ℝ) * ε) ω := by
    change
      (⨅ (t : ℝ≥0) (_ : (((n + 1 : ℕ) : ℝ) * ε) < X.X t ω),
        (t : ℝ≥0∞)) ≤
      (⨅ (t : ℝ≥0) (_ : (((n + 2 : ℕ) : ℝ) * ε) < X.X t ω),
        (t : ℝ≥0∞))
    exact firstUpcrossing_threshold_iInf_mono X ω _ _ hlevel
  exact lt_of_le_of_lt htime hSurvive
