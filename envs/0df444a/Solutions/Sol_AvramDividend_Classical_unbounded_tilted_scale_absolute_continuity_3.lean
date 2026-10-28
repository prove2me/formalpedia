-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_scale_absolute_continuity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T18:34:25.718774+00:00
-- url     : https://prove2.me/submissions/94176500-81db-48f8-a53b-b055c6995d7c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv with
    hσ | hsmall
  · exact esscher_tilted_scale_C1_of_positive_gaussian_without_standing
      X q hq W hW hσ φ hφ hroot V hV
  · exact esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hsmall φ hφ hroot V hV
