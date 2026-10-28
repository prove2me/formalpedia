-- Prove2me | solution 8 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T13:17:46.38103+00:00
-- url     : https://prove2.me/submissions/ef8e8ed3-9345-4035-981d-7baa46dbae7f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop_of_eventually_ge_exp
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  exact AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_eventually_ge_exp
    X hX q hq W hW
    (AvramDividend.Classical.scaleDeriv_eventually_ge_exp X hX q hq W hW)
