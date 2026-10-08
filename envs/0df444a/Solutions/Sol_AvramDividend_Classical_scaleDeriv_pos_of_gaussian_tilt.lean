-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_pos_of_gaussian_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T20:37:08.914753+00:00
-- url     : https://prove2.me/submissions/ed72182a-f8cd-4363-b27c-4ed0ad7564f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  have hpositive : ∀ x : ℝ, 0 < x → 0 < W x := by
    intro x hx
    exact scaleFunction_strict_pos_of_gaussian X q W hW hσ x hx
  exact scale_deriv_pos_of_normalized_monotone
    W φ hφ hpositive htilt hdiff
