-- Prove2me | solution 1 for AvramDividend.Classical.chat03_both_infinite_passage_event_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T23:20:38.534798+00:00
-- url     : https://prove2.me/submissions/bb5e190e-4210-44f4-bede-c8007376cc41

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff
import Theorems.Thm_AvramDividend_Classical_chat03_countable_grid_exit_event_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_named_exit_finite_infinite_interface
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Both exact named strict passage times being infinite is equivalent
to the complement of an already Proved measurable countable grid exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower upper : ℝ) :
    MeasurableSet
      {ω : Ω |
        twoSidedExitUpTime X upper ω = ∞ ∧
        twoSidedExitDownTime X lower ω = ∞} := by
  have hGrid :=
    chat03_countable_grid_exit_event_measurable X lower upper
  have hEq :
      {ω : Ω | twoSidedExitUpTime X upper ω = ∞ ∧
        twoSidedExitDownTime X lower ω = ∞} =
      {ω : Ω | ¬ ∃ n : ℕ, 0 < n ∧ ∃ k : ℕ,
        X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω < lower ∨
        upper < X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω} := by
    ext ω
    obtain ⟨_, _, hUp, hDown⟩ :=
      chat03_two_sided_named_exit_finite_infinite_interface X upper lower ω
    have hWit :=
      chat03_countable_inverse_nat_grid_exit_iff X ω lower upper
    constructor
    · intro both hgrid
      obtain ⟨t, hExit⟩ := hWit.mpr hgrid
      rcases hExit with hl | hr
      · exact hDown.mp both.2 ⟨t, hl⟩
      · exact hUp.mp both.1 ⟨t, hr⟩
    · intro noGrid
      have noCont : ¬∃ t : ℝ≥0,
          X.X t ω < lower ∨ upper < X.X t ω :=
        fun h => noGrid (hWit.mp h)
      constructor
      · apply hUp.mpr
        rintro ⟨t, hr⟩
        exact noCont ⟨t, Or.inr hr⟩
      · apply hDown.mpr
        rintro ⟨t, hl⟩
        exact noCont ⟨t, Or.inl hl⟩
  rw [hEq]
  exact hGrid.compl
