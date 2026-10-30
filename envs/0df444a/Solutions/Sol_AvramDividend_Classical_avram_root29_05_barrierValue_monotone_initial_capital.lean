-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierValue_monotone_initial_capital
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:22:23.002986+00:00
-- url     : https://prove2.me/submissions/ebc17a49-4a94-4e01-9924-cc27bde1b3cb

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The original reflected-regulator killed dividend value increases with
initial capital below a common positive barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (a x y : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x)
    (hxy : x ≤ y) (hya : y ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤
      dividendValue X q y (barrierStrategy X y a) := by
  have hxa : x ≤ a := le_trans hxy hya
  have hy0 : 0 ≤ y := le_trans hx0 hxy
  have hExit : twoSidedExitExpectation X q a x ≤
      twoSidedExitExpectation X q a y :=
    chat04_discounted_strict_exit_monotone_initial_reserve
      X q a x y (le_of_lt hq) hxy
  have hVx :=
    barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  have hVy :=
    barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a y ha hy0 hya
  change dividendValue X q x (barrierStrategy X x a) =
      twoSidedExitExpectation X q a x * barrierSupValue X a q at hVx
  change dividendValue X q y (barrierStrategy X y a) =
      twoSidedExitExpectation X q a y * barrierSupValue X a q at hVy
  rw [hVx, hVy]
  gcongr
