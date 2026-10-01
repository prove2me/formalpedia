-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_continuous_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T16:56:02.436345+00:00
-- url     : https://prove2.me/submissions/8f19524e-f688-4793-b40f-a448954f9dbb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) ∧
      Tendsto (deriv W) atTop atTop := by
  exact ⟨scaleDeriv_continuous X hX q hq W hW,
    scaleDeriv_tendsto_atTop X hX q hq W hW⟩
