-- Prove2me | solution 4 for AvramDividend.Classical.barrier_cstar_attains_value_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:22:16.511003+00:00
-- url     : https://prove2.me/submissions/c476161d-1504-428d-be5b-1a674c98e267
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_above_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Split the all-capital c-star dividend valuation into its disjoint capital regions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
  intro x hx
  by_cases hxc : x ≤ (cstar W).toReal
  · exact barrier_cstar_attains_value_below_barrier
      X hX q hq W hW hc x hx hxc
  · exact barrier_cstar_attains_value_above_barrier
      X hX q hq W hW hc x (lt_of_not_ge hxc)
