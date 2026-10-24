-- Prove2me | solution 1 for AvramDividend.Classical.chat04_corrected_twoSidedExitExpectation_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T14:22:06.885934+00:00
-- url     : https://prove2.me/submissions/640970d5-a8ca-4cc5-8b9f-9ced2bbbe9ee

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_antitone_discount
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The corrected strict killed exit expectation also decreases
with discount, via the proved definitional-equivalence bridge. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q₁ q₂ a x : ℝ) (hq : q₁ ≤ q₂) :
    twoSidedExitExpectationCorrected X q₂ a x ≤
      twoSidedExitExpectationCorrected X q₁ a x := by
  calc
    twoSidedExitExpectationCorrected X q₂ a x =
        twoSidedExitExpectation X q₂ a x :=
      (chat04_twoSidedExitExpectation_eq_corrected X q₂ a x).symm
    _ ≤ twoSidedExitExpectation X q₁ a x :=
      chat04_twoSidedExitExpectation_antitone_discount X q₁ q₂ a x hq
    _ = twoSidedExitExpectationCorrected X q₁ a x :=
      chat04_twoSidedExitExpectation_eq_corrected X q₁ a x
