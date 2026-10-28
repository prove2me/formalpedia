-- Prove2me | solution 4 for AvramDividend.Classical.barrier_strategy_value_above_positive_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:35:08.177132+00:00
-- url     : https://prove2.me/submissions/3d296fb8-4abd-48e6-9c3b-40c469a10949
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_eq_scale_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_for_nonnegative_capital

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
  -- Reduction via the Proved above-barrier lifting lemma: the value above the
  -- barrier follows from the boundary value at a plus the lump sum, both packaged
  -- in `barrierStrategy_above_value_of_boundary` (Proved). The boundary value is
  -- the Open scale-ratio identity f9580183 transported across the definitional
  -- unfolding `barrierValue W a a = W a / deriv W a`; nonnegativity is Proved.
  -- Principal lemma: barrierStrategy_above_value_of_boundary (Proved).
  -- Exact unresolved identity at this level: boundary scale ratio f9580183 (Open).
  have ha0 : a ≠ 0 := ne_of_gt ha
  have h2 : barrierValue W a a = W a / deriv W a := by
    -- CE repair (parent 14549, E01 UNSOLVED_GOALS): the inner `a \u2264 a` reduces to
    -- `ite True`, which needs `if_true`; `sub_zero` covers residual arithmetic.
    simp only [barrierValue, scaleDeriv, divE, ha0, if_false, if_true,
      not_lt_of_ge ha.le, le_refl, EReal.coe_ne_top, EReal.toReal_coe, sub_zero]
  -- Boundary via the history-backed supValue route (f9580183 has no prepared
  -- module: zero submission history, so its import is unresolvable at admission).
  have hsup : barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) :=
    AvramDividend.Classical.barrierSupValue_eq_scale_ratio X hX q hq W hW a ha
  have hself : dividendValue X q a (barrierStrategy X a a) =
      barrierSupValue X a q :=
    AvramDividend.Classical.barrierValue_self_eq_barrierSupValue X q a
  have hboundary : dividendValue X q a (barrierStrategy X a a) =
      ENNReal.ofReal (barrierValue W a a) := by
    rw [hself, hsup, ← h2]
  have hval : 0 ≤ barrierValue W a a :=
    AvramDividend.Classical.barrierValue_nonnegative_for_nonnegative_capital
      X hX q hq W hW a a ha.le ha.le
  exact AvramDividend.Classical.barrierStrategy_above_value_of_boundary
    X q W a x ha.le hax hboundary hval
