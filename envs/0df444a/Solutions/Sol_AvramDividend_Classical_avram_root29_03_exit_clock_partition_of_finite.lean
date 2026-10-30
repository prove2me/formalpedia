-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_exit_clock_partition_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:12:11.91788+00:00
-- url     : https://prove2.me/submissions/005a5e98-e621-4092-8c7d-34b079d7a68b

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Disjoint strict exit orders cover precisely paths with a finite actual
exit clock. The excluded complement comprises both clocks at infinity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    (twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω ∨
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a - x) ω) ↔
    (twoSidedExitUpTime X (a - x) ω < ⊤ ∨
      twoSidedExitDownTime X (-x) ω < ⊤) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (lt_of_lt_of_le h le_top)
    · exact Or.inr (lt_of_lt_of_le h le_top)
  · intro hFinite
    rcases lt_trichotomy
      (twoSidedExitUpTime X (a - x) ω)
      (twoSidedExitDownTime X (-x) ω) with hUp | hEq | hDown
    · exact Or.inl hUp
    · have hUpFinite : twoSidedExitUpTime X (a - x) ω < ⊤ := by
        rcases hFinite with hu | hd
        · exact hu
        · simpa only [hEq] using hd
      have hNotTop : twoSidedExitUpTime X (a - x) ω ≠ ⊤ :=
        ne_of_lt hUpFinite
      have hUpClock : twoSidedExitUpTime X (a - x) ω =
          ((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hNotTop).symm
      have hDownClock : twoSidedExitDownTime X (-x) ω =
          ((twoSidedExitUpTime X (a - x) ω).toNNReal : ℝ≥0∞) :=
        hEq.symm.trans hUpClock
      exfalso
      exact chat03_official_strict_passage_no_finite_ties
        X ω (-x) (a - x) (by linarith [ha])
        (twoSidedExitUpTime X (a - x) ω).toNNReal hUpClock hDownClock
    · exact Or.inr hDown
