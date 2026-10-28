-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_tilted_scale_absolute_continuity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T16:48:22.838125+00:00
-- url     : https://prove2.me/submissions/8aa788ee-c0bf-46b6-9cf2-163e8c998e0e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_positive_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The unbounded-variation tilted scale is C¹ by the Gaussian/infinite-jump dichotomy. -/
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
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv
    with hσ | hvar
  · exact esscher_tilted_scale_C1_of_positive_gaussian_without_standing
      X q hq W hW hσ φ hφ hroot V hV
  · exact esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hvar φ hφ hroot V hV
