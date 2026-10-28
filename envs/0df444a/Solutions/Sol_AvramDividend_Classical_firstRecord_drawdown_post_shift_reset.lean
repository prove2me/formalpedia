-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_drawdown_post_shift_reset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:58:52.301988+00:00
-- url     : https://prove2.me/submissions/f9b177ac-202a-4208-b9b9-f86cb210e37a

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_runningSup_sub_path_eq_zero
import Theorems.Thm_AvramDividend_Classical_drawdown_after_firstUpcrossing_shift

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Drawdown restarts from zero at an attained strict upper record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u)) :
    ∀ t : ℝ≥0,
      runningSup X (u + t) ω - X.X (u + t) ω =
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X (u + t) ω := by
  intro t
  have hu' : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b - 0 < X.X s ω), (s : ℝ≥0∞)) := by
    simpa only [sub_zero] using hu
  have hDraw := drawdown_after_firstUpcrossing_shift
    X 0 b hb ω u hu' hBdd t
  have hZero :=
    firstUpcrossing_runningSup_sub_path_eq_zero X b hb ω u hu
  rw [hZero, zero_add] at hDraw
  exact hDraw
