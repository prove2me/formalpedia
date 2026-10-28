-- Prove2me | solution 2 for AvramDividend.Classical.barrier_strategy_value_zero_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:41:45.851743+00:00
-- url     : https://prove2.me/submissions/ac312c0e-f61e-4070-8711-2f2d11208f6e
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
  -- Zero-barrier value by excess decomposition: above 0 the strategy is the
  -- lump sum plus reflection at 0 (Proved ece035bb); the lump-sum value splits off
  -- (Proved 9edc31be, admissible by Proved 32b4ccb8); the value at 0 is the
  -- CE repair (parent 14552, E01-E03 TYPE_MISMATCH): bare `le_refl` in term
  -- position takes an explicit argument in this Mathlib revision; supply `(0)`.
  -- zero-boundary package (Open 027a50fd, history-backed module); the barrier
  -- function at 0 is definitionally x + its value at 0.
  -- Principal lemmas: add_initial_excess_admissible_value (Proved),
  -- barrier_zero_boundary_value_package (Open).
  -- Exact unresolved identity: 027a50fd zero-boundary package (Open).
  have hpack := AvramDividend.Classical.barrier_zero_boundary_value_package
    X hX q hq W hW
  rcases eq_or_lt_of_le hx with rfl | hpos
  · exact hpack.2
  · have hstrat : barrierStrategy X x 0 =
        (fun t ω => if t = 0 then 0 else (x - 0) + barrierStrategy X 0 0 t ω) :=
      AvramDividend.Classical.barrierStrategy_eq_add_initial_excess_above_barrier
        X x 0 (le_refl 0) hpos
    have hE : IsAdmissibleLe X 0 (ENNReal.ofReal 0) (barrierStrategy X 0 0) :=
      AvramDividend.Classical.barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl 0) (le_refl 0)
    -- CE repair r3 (parent 14558, E01): the remaining term-position `le_refl`
    -- (the `hc : 0 \u2264 0` argument) takes explicit `(0)`, as in r2.
    have hadd := AvramDividend.Classical.add_initial_excess_admissible_value
      X q x 0 (le_refl 0) hpos (barrierStrategy X 0 0) hE
    have hD : dividendValue X q x (barrierStrategy X x 0) =
        ENNReal.ofReal (x - 0) +
          dividendValue X q 0 (barrierStrategy X 0 0) := by
      rw [hstrat]
      exact hadd.2
    have hBV : x + barrierValue W 0 0 = barrierValue W 0 x := by
      simp only [barrierValue, scaleDeriv, divE, not_lt_of_ge hx,
        not_le_of_gt hpos, lt_irrefl, le_refl, if_false, if_true, sub_zero]
    have hfin : ENNReal.ofReal (x - 0) +
        ENNReal.ofReal (barrierValue W 0 0) =
        ENNReal.ofReal (barrierValue W 0 x) := by
      rw [sub_zero, ← ENNReal.ofReal_add hx hpack.1, hBV]
    rw [hD, hpack.2]
    exact hfin
