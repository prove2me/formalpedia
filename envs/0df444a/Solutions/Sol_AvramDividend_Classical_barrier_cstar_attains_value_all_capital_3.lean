-- Prove2me | solution 3 for AvramDividend.Classical.barrier_cstar_attains_value_all_capital
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T13:24:09.055978+00:00
-- url     : https://prove2.me/submissions/10e9dd69-7b7f-4819-bbf2-fae425cab4c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrier_cstar_attains_value_above_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
  intro x hx
  rcases le_or_gt x (cstar W).toReal with hxc | hcx
  · exact AvramDividend.Classical.barrier_cstar_attains_value_below_barrier
      X hX q hq W hW hc x hx hxc
  · exact AvramDividend.Classical.barrier_cstar_attains_value_above_barrier
      X hX q hq W hW hc x hcx
