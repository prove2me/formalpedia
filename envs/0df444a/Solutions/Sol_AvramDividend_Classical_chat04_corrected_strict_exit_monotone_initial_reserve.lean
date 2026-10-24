-- Prove2me | solution 1 for AvramDividend.Classical.chat04_corrected_strict_exit_monotone_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:13:54.599813+00:00
-- url     : https://prove2.me/submissions/d2f7a2d8-9763-4a01-bc17-5b90a8ca9ec9

import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Corrected and original strict killed exit transforms share reserve monotonicity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x y : ℝ)
    (hq : 0 ≤ q) (hxy : x ≤ y) :
    twoSidedExitExpectationCorrected X q a x ≤
      twoSidedExitExpectationCorrected X q a y := by
  calc
    twoSidedExitExpectationCorrected X q a x =
        twoSidedExitExpectation X q a x :=
          (chat04_twoSidedExitExpectation_eq_corrected X q a x).symm
    _ ≤ twoSidedExitExpectation X q a y :=
          chat04_discounted_strict_exit_monotone_initial_reserve X q a x y hq hxy
    _ = twoSidedExitExpectationCorrected X q a y :=
          chat04_twoSidedExitExpectation_eq_corrected X q a y
