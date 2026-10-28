-- Prove2me | solution 1 for AvramDividend.Classical.firstBadClock_shift_of_no_early_breach
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:20:00.816194+00:00
-- url     : https://prove2.me/submissions/f3a44efb-ef42-4f54-8248-c3a788800d3e

import Mathlib.Data.ENNReal.Operations
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
open scoped NNReal ENNReal
theorem solution
    (u : ℝ≥0) (bad shiftedBad : ℝ≥0 → Prop)
    (hpre : ∀ s : ℝ≥0, s < u → ¬ bad s)
    (hpost : ∀ t : ℝ≥0, bad (u + t) ↔ shiftedBad t) :
    (⨅ (s : ℝ≥0) (_ : bad s), (s : ℝ≥0∞)) =
      (u : ℝ≥0∞) +
        (⨅ (t : ℝ≥0) (_ : shiftedBad t), (t : ℝ≥0∞)) := by
  rw [ENNReal.add_iInf]
  apply le_antisymm
  · refine le_iInf fun t => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun ht => ?_
    refine (iInf₂_le (u + t) ((hpost t).2 ht)).trans ?_
    simp
  · refine le_iInf fun s => le_iInf fun hs => ?_
    have hus : u ≤ s := by
      by_contra h; exact hpre s (lt_of_not_ge h) hs
    obtain ⟨t, rfl⟩ : ∃ t, s = u + t := ⟨s - u, (add_tsub_cancel_of_le hus).symm⟩
    refine (iInf_le _ t).trans ?_
    rw [ENNReal.add_iInf]
    refine (iInf_le _ ((hpost t).1 hs)).trans ?_
    simp
