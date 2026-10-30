-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_lower_first_iff_finite_stopped_min
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:48:31.388862+00:00
-- url     : https://prove2.me/submissions/ff302070-c74d-465a-a709-010979f5aa43

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Strict lower-first passage equals attainment of the actual finite
two-sided minimum exit clock. Finite ties are excluded by the proved
original-process no-finite-simultaneous-passage theorem. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω ↔
    min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
      twoSidedExitDownTime X (-x) ω ∧
    twoSidedExitDownTime X (-x) ω < ⊤ := by
  constructor
  · intro hDown
    exact ⟨min_eq_right (le_of_lt hDown), lt_of_lt_of_le hDown le_top⟩
  · rintro ⟨hMin, hFinite⟩
    have hLe : twoSidedExitDownTime X (-x) ω ≤
        twoSidedExitUpTime X (a - x) ω :=
      (min_eq_right_iff).mp hMin
    rcases lt_or_eq_of_le hLe with hDown | hTie
    · exact hDown
    · have hNotTop : twoSidedExitDownTime X (-x) ω ≠ ⊤ :=
        ne_of_lt hFinite
      have hDownClock : twoSidedExitDownTime X (-x) ω =
          ((twoSidedExitDownTime X (-x) ω).toNNReal : ℝ≥0∞) :=
        (ENNReal.coe_toNNReal hNotTop).symm
      have hUpClock : twoSidedExitUpTime X (a - x) ω =
          ((twoSidedExitDownTime X (-x) ω).toNNReal : ℝ≥0∞) :=
        hTie.symm.trans hDownClock
      exfalso
      exact chat03_official_strict_passage_no_finite_ties
        X ω (-x) (a - x) (by linarith [ha])
        (twoSidedExitDownTime X (-x) ω).toNNReal hUpClock hDownClock
