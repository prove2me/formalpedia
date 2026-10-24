-- Prove2me | solution 1 for AvramDividend.Classical.barrierStrategy_above_value_of_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:44:44.247732+00:00
-- url     : https://prove2.me/submissions/ec7c69ba-b7ea-44da-b651-218d85dd4d62

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The initial barrier payment propagates a boundary-value identity above the barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (a x : ℝ) (ha : 0 ≤ a) (hax : a < x)
    (hboundary : dividendValue X q a (barrierStrategy X a a) =
      ENNReal.ofReal (barrierValue W a a))
    (hval : 0 ≤ barrierValue W a a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by
  have hvalsum :=
    (add_initial_excess_admissible_value X q x a ha hax
      (barrierStrategy X a a)
      (barrierStrategy_admissibleLe_nonnegative_barrier X a a ha ha)).2
  rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha hax]
  rw [hvalsum, hboundary, barrierValue_above_affine W a x ha hax]
  exact (ENNReal.ofReal_add (le_of_lt (sub_pos.mpr hax)) hval).symm
