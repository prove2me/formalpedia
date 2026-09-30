-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T23:07:29.982288+00:00
-- url     : https://prove2.me/submissions/85287ae1-7d23-4609-b6a1-06f2d785110a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Tendsto (deriv W) atTop atTop := by
  rcases scaleDeriv_eventually_ge_exp X hX q hq W hW with
    ⟨φ, c, hφ, hc, hdom⟩
  apply tendsto_atTop_mono' atTop hdom
  exact
    (Real.tendsto_exp_comp_atTop.mpr (tendsto_id.const_mul_atTop hφ)).const_mul_atTop hc
