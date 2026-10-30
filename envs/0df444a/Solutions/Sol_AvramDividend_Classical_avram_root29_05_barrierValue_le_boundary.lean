-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierValue_le_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:22:18.301701+00:00
-- url     : https://prove2.me/submissions/d878227f-c224-4cf7-84ea-ad9a7e82c487

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine killed reflected regulator value below the barrier is bounded
by its boundary value, via the first-upcrossing discount in the original law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤ barrierSupValue X a q := by
  have hDiscount : twoSidedExitExpectation X q a x ≤ 1 :=
    chat04_twoSidedExitExpectation_le_one X q a x (le_of_lt hq)
  have hValue :=
    barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  change dividendValue X q x (barrierStrategy X x a) =
      twoSidedExitExpectation X q a x * barrierSupValue X a q at hValue
  rw [hValue]
  calc
    twoSidedExitExpectation X q a x * barrierSupValue X a q
        ≤ (1 : ℝ≥0∞) * barrierSupValue X a q := by
          gcongr
    _ = barrierSupValue X a q := one_mul _
