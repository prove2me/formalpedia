-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation_of_unbounded
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:13:04.554643+00:00
-- url     : https://prove2.me/submissions/4af62ad2-9100-49b5-bf1a-e945775befa9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact Gaussian/infinite-small-jump split of unbounded variation,
using the already Proved model-level dichotomy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧ NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv with
    hσ | hvar
  · exact scaleFunction_excursion_tail_derivative_representation_of_gaussian
      X hX q hq W hW hσ
  · exact scaleFunction_excursion_tail_derivative_representation_of_infinite_small_jump
      X hX q hq W hW hvar
