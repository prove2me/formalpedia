-- Prove2me | solution 1 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:07:55.924039+00:00
-- url     : https://prove2.me/submissions/bf3fac3b-4c9c-499e-99e2-4535d435c227
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_eq_add_initial_excess_above_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
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
    (x : ℝ) (hx : 0 ≤ x) :
    dividendValue X q x (barrierStrategy X x 0) =
      ENNReal.ofReal (barrierValue W 0 x) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · exact (AvramDividend.Classical.barrier_zero_boundary_value_package
      X hX q hq W hW).2
  · have hE :
        IsAdmissibleLe X 0 (ENNReal.ofReal 0) (barrierStrategy X 0 0) :=
      AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 le_rfl le_rfl
    have hsplit :=
      (AvramDividend.Classical.add_initial_excess_admissible_value
        X q x 0 le_rfl hxpos (barrierStrategy X 0 0) hE).2
    have hstrategy :=
      AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
        X x 0 le_rfl hxpos
    obtain ⟨hbnonneg, hbzero⟩ :=
      AvramDividend.Classical.barrier_zero_boundary_value_package
        X hX q hq W hW
    rw [hstrategy, hsplit, hbzero]
    have hbar :
        barrierValue W 0 x = x + barrierValue W 0 0 := by
      simp [barrierValue, hx, not_le.mpr hxpos]
    rw [hbar, ENNReal.ofReal_add hx hbnonneg]
    simpa only [sub_zero]
