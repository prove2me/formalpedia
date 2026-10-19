-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_continuous_tendsto_atTop
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-18T18:51:31.864979+00:00
-- url     : https://prove2.me/submissions/4ad21b94-35bc-4c4a-a51e-bdfaa65b9829
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact published conjunction, conditional on two still-Open children. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) ∧
      Filter.Tendsto (deriv W) Filter.atTop Filter.atTop := by
  exact ⟨
    scaleDeriv_continuous X hX q hq W hW,
    scaleDeriv_tendsto_atTop X hX q hq W hW⟩
