-- Prove2me | solution 9 for AvramDividend.Classical.cstar_lt_top
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:49:19.255468+00:00
-- url     : https://prove2.me/submissions/c4101c4d-1951-4b4a-af19-670d062edc9a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_deriv_continuous_positive_axis_growth

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    cstar W < ⊤ := by
  have hregular : ContDiffOn ℝ 1 W (Set.Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one X hX q hq W hW
  have hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ)) :=
    hregular.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hgrowth : Tendsto (deriv W) Filter.atTop Filter.atTop :=
    scaleDeriv_tendsto_atTop X hX q hq W hW
  exact cstar_finite_of_deriv_continuous_positive_axis_growth W hcont hgrowth
