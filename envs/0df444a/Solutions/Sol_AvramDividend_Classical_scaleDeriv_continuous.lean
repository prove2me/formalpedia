-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T22:40:10.827117+00:00
-- url     : https://prove2.me/submissions/68e7e0eb-9918-4749-b6c5-89841e845238
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
  obtain ⟨_, _, h33⟩ := hX
  cases h33 with
  | inl hσ =>
      exact scaleDeriv_continuous_of_gaussian X hσ q hq W hW
  | inr hrest =>
      cases hrest with
      | inl hvar =>
          exact scaleDeriv_continuous_of_unbounded_variation X hvar q hq W hW
      | inr hac =>
          exact scaleDeriv_continuous_of_ac_levy X hac q hq W hW
