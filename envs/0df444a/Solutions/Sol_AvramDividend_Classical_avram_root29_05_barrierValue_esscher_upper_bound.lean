-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_barrierValue_esscher_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:22:26.954477+00:00
-- url     : https://prove2.me/submissions/fe858cfc-17b3-4a0f-950a-059eee434aeb

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_killed_exit_mul_supValue
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An Esscher-root exponential envelope for the original strict-ruin
killed reflected-regulator dividend value below a common barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    dividendValue X q x (barrierStrategy X x a) ≤
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) *
        barrierSupValue X a q := by
  have hExit : twoSidedExitExpectation X q a x ≤
      ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by
    rw [chat04_twoSidedExitExpectation_eq_corrected X q a x]
    exact corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot a x ha hx0 hxa
  have hValue :=
    barrierStrategy_value_eq_killed_exit_mul_supValue
      X hX q hq a x ha hx0 hxa
  change dividendValue X q x (barrierStrategy X x a) =
      twoSidedExitExpectation X q a x * barrierSupValue X a q at hValue
  rw [hValue]
  gcongr
