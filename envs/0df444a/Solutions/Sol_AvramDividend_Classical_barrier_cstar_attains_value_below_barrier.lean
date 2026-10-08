-- Prove2me | solution 1 for AvramDividend.Classical.barrier_cstar_attains_value_below_barrier
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:48:12.034502+00:00
-- url     : https://prove2.me/submissions/9c04b04f-bd92-4c3c-b346-143bd133d792
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_admissible
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_cstar_value_all_capital

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) :
    ∀ x : ℝ, 0 ≤ x → x ≤ (cstar W).toReal →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x) := by
  intro x hx _
  exact ⟨
    AvramDividend.Classical.barrierStrategy_cstar_admissible X hX W hc x hx,
    AvramDividend.Classical.barrierStrategy_cstar_value_all_capital
      X hX q hq W hW hc x hx
  ⟩
