-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_strict_up_event_iff_finite_weak_order
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:07:30.035989+00:00
-- url     : https://prove2.me/submissions/6789350d-2296-45c8-af1e-57a9d71daf74

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual strict upper-first exit event is exactly finite weak-clock
ordering. Separated barriers exclude finite clock ties pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω ↔
      twoSidedExitUpTime X (a - x) ω ≤
        twoSidedExitDownTime X (-x) ω ∧
      twoSidedExitUpTime X (a - x) ω < ⊤ := by
  constructor
  · intro h
    exact ⟨le_of_lt h, lt_of_lt_of_le h le_top⟩
  · rintro ⟨hLe, hFin⟩
    rcases lt_or_eq_of_le hLe with hLt | hEq
    · exact hLt
    · have hNe : twoSidedExitUpTime X (a - x) ω ≠ ⊤ :=
        ne_of_lt hFin
      have hUp : twoSidedExitUpTime X (a - x) ω =
          ((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hNe).symm
      have hDown : twoSidedExitDownTime X (-x) ω =
          ((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0∞) :=
        hEq.symm.trans hUp
      exfalso
      exact chat03_official_strict_passage_no_finite_ties
        X ω (-x) (a - x) (by linarith [ha])
        (twoSidedExitUpTime X (a - x) ω).toNNReal hUp hDown
