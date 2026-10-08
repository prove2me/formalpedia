-- Prove2me | solution 3 for AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:57:31.053345+00:00
-- url     : https://prove2.me/submissions/828cacfb-ae9d-491b-9059-d755249d8a45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_add_initial_excess_admissible_value

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hax : a < x) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (barrierValue W a x) := by
  have ha0 : 0 ≤ a := le_of_lt ha
  have hE : IsAdmissibleLe X a (ENNReal.ofReal a)
        (barrierStrategy X a a) :=
    barrierStrategy_admissibleLe_nonnegative_barrier X a a ha0 ha0
  have hsplit :=
    (add_initial_excess_admissible_value X q x a ha0 hax
      (barrierStrategy X a a) hE).2
  have hboundary :
      dividendValue X q a (barrierStrategy X a a) =
        ENNReal.ofReal (barrierValue W a a) := by
    have h := barrier_strategy_value X hX q hq W hW a ha a ha0 (le_refl a)
    simpa [barrierValue_at_positive_barrier_eq_deriv_ratio W a ha] using h
  have hpos : 0 ≤ barrierValue W a a := by
    rw [barrierValue_at_positive_barrier_eq_deriv_ratio W a ha]
    exact div_nonneg (hW.2.1 a ha0)
      (le_of_lt (scaleDeriv_pos X hX q hq W hW a ha))
  have hx_minus : 0 ≤ x - a := sub_nonneg.mpr (le_of_lt hax)
  have haff : barrierValue W a x = (x - a) + barrierValue W a a :=
    barrierValue_above_affine W a x ha0 hax
  rw [barrierStrategy_eq_add_initial_excess_above_barrier X x a ha0 hax]
  rw [hsplit, hboundary, haff]
  exact (ENNReal.ofReal_add hx_minus hpos).symm
