-- Prove2me | solution 8 for AvramDividend.Classical.unbounded_tilted_scale_absolute_continuity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T06:54:21.424676+00:00
-- url     : https://prove2.me/submissions/0224266c-3ef7-4822-8dee-98d0f688bd44
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

/-!
Authoritative DEC4 route for `unbounded_tilted_scale_absolute_continuity` (0883):
Proved cb0b01e6 splits UBV into Gaussian (0 < σ) vs infinite-small-jump moment;
Proved d5b62f36 closes the Gaussian leg; Open 6344b1a4 closes the infinite-jump leg.
At best SKETCH_ACCEPTED until 6344b1a4 is proved; advances the UBV absolute-continuity leg.
-/

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
  have hDisj :=
    unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv
  rcases hDisj with hσ | hvar
  · exact esscher_tilted_scale_C1_of_positive_gaussian_without_standing
      X q hq W hW hσ φ hφ hroot V hV
  · exact esscher_tilted_scale_C1_of_infinite_small_jump_without_standing
      X q hq W hW hvar φ hφ hroot V hV
