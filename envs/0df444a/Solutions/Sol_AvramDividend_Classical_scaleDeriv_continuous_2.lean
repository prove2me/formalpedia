-- Prove2me | solution 2 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:41:09.086136+00:00
-- url     : https://prove2.me/submissions/4cba3ad8-9ea7-49e6-bc93-1afce84c422b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_ac_levy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ContinuousOn (deriv W) (Ioi 0) := by
  rcases hX.2.2 with hσ | hrest
  · exact scaleDeriv_continuous_of_gaussian X hσ q hq W hW
  · rcases hrest with hvar | hac
    · exact scaleDeriv_continuous_of_unbounded_variation X hvar q hq W hW
    · exact scaleDeriv_continuous_of_ac_levy X hac q hq W hW
