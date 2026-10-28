-- Prove2me | solution 1 for AvramDividend.Classical.firstRecord_shifted_drawdown_survival_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:05:14.162547+00:00
-- url     : https://prove2.me/submissions/91f6f561-030a-406c-b9a6-b5aa9d243d59

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstRecord_drawdown_post_shift_reset
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Future drawdown survival is a pure shifted-path event after a record. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b : ℝ) (hb : 0 ≤ b) (ω : Ω) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (hBdd : BddAbove ((fun r : ℝ≥0 => X.X r ω) '' Set.Icc 0 u))
    (a : ℝ) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t ≤ T → reflectedSup X (u + t) ω ≤ a) ↔
      (∀ t : ℝ≥0, t ≤ T →
        sSup ((fun r : ℝ≥0 => X.X (u + r) ω) '' Set.Icc 0 t) -
          X.X (u + t) ω ≤ a) := by
  have hReset := firstRecord_drawdown_post_shift_reset
    X b hb ω u hu hBdd
  constructor
  · intro h t ht
    have hAt := h t ht
    change runningSup X (u + t) ω - X.X (u + t) ω ≤ a at hAt
    rwa [hReset t] at hAt
  · intro h t ht
    change runningSup X (u + t) ω - X.X (u + t) ω ≤ a
    rw [hReset t]
    exact h t ht
