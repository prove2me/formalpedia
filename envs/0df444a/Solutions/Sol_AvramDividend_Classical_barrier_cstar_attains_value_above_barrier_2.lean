-- Prove2me | solution 2 for AvramDividend.Classical.barrier_cstar_attains_value_above_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T23:10:25.00691+00:00
-- url     : https://prove2.me/submissions/5f575991-fb2b-46a2-886b-ca2dc218c06d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_admissible
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_above_positive_barrier
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite optimal-barrier admissibility is already established. The value
identity follows by splitting the strictly positive and zero cap regimes. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, (cstar W).toReal < x →
      IsAdmissibleLe X x (cstar W)
        (barrierStrategy X x (cstar W).toReal) ∧
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by
  intro x hax
  have hc0 : 0 ≤ (cstar W).toReal := ENNReal.toReal_nonneg
  have hx0 : 0 ≤ x := le_trans hc0 hax.le
  refine ⟨barrierStrategy_cstar_admissible X hX W hc x hx0, ?_⟩
  by_cases hzero : (cstar W).toReal = 0
  · have hvalue :
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (barrierValue W (cstar W).toReal x) := by
      rw [hzero]
      exact barrier_strategy_value_zero_all_capital X hX q hq W hW x hx0
    simpa only [vcstar] using hvalue
  · have hpos : 0 < (cstar W).toReal :=
      lt_of_le_of_ne hc0 (Ne.symm hzero)
    have hvalue := barrier_strategy_value_above_positive_barrier
      X hX q hq W hW (cstar W).toReal x hpos hax
    simpa only [vcstar] using hvalue
