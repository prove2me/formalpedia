-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_excursion_tail_derivative_representation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T15:17:34.879069+00:00
-- url     : https://prove2.me/submissions/6997bcd4-865e-4a6c-b051-86d30a1b3307
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_unbounded
import Theorems.Thm_AvramDividend_Classical_scaleFunction_excursion_tail_derivative_representation_of_bv_ac

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ (φ : ℝ) (μ : Measure ℝ),
      0 < φ ∧
      NullSingletonClass μ ∧
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) ∧
      (∀ x : ℝ, 0 < x →
        deriv W x = W x * (φ + μ.real (Ici x))) := by
  by_cases hbv : X.BoundedVariation
  · have hac : X.ν ≪ volume :=
      standing_bv_levy_absolutely_continuous X hX hbv
    exact scaleFunction_excursion_tail_derivative_representation_of_bv_ac
      X hX q hq W hW hbv hac
  · exact scaleFunction_excursion_tail_derivative_representation_of_unbounded
      X hX q hq W hW hbv
