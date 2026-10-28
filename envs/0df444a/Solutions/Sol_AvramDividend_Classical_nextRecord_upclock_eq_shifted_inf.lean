-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_upclock_eq_shifted_inf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:06:18.859948+00:00
-- url     : https://prove2.me/submissions/b04ebcb0-8bd7-4725-afc0-865ac55b7607

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_nextRecord_upclock_le_shifted_witness
import Theorems.Thm_AvramDividend_Classical_nextRecord_crossing_after_firstRecord
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The actual next record clock is the infimum of shifted crossing witnesses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b ε : ℝ) (hε : 0 ≤ ε) (u : ℝ≥0) (ω : Ω)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hAt : X.X u ω = b) :
    twoSidedExitUpTime X (b + ε) ω =
      (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω),
        ((u + t : ℝ≥0) : ℝ≥0∞)) := by
  apply le_antisymm
  · change twoSidedExitUpTime X (b + ε) ω ≤
        (⨅ (t : ℝ≥0)
          (_ : ε < X.X (u + t) ω - X.X u ω),
          ((u + t : ℝ≥0) : ℝ≥0∞))
    refine le_iInf fun t => le_iInf fun hNext => ?_
    exact nextRecord_upclock_le_shifted_witness
      X b ε u t ω hAt hNext
  · change (⨅ (t : ℝ≥0)
        (_ : ε < X.X (u + t) ω - X.X u ω),
        ((u + t : ℝ≥0) : ℝ≥0∞)) ≤
        (⨅ (s : ℝ≥0) (_ : b + ε < X.X s ω), (s : ℝ≥0∞))
    refine le_iInf fun s => le_iInf fun hCross => ?_
    obtain ⟨hus, hShift⟩ :=
      nextRecord_crossing_after_firstRecord
        X b ε hε u s ω hu hAt hCross
    have hTime : u + (s - u) = s := add_tsub_cancel_of_le hus
    have hCrossShift :
        ε < X.X (u + (s - u)) ω - X.X u ω := by
      simpa [hTime] using hShift
    have hBound :
        (⨅ (t : ℝ≥0)
          (_ : ε < X.X (u + t) ω - X.X u ω),
          ((u + t : ℝ≥0) : ℝ≥0∞)) ≤
          ((u + (s - u) : ℝ≥0) : ℝ≥0∞) :=
      iInf_le_of_le (s - u) (iInf_le_of_le hCrossShift le_rfl)
    simpa [hTime] using hBound
