-- Prove2me | solution 1 for AvramDividend.Classical.hjb_pointwise_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T09:57:50.676074+00:00
-- url     : https://prove2.me/submissions/628278c8-44fa-4ccf-9891-2d214362cb57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (y : ℝ)
    (hmax : max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by
  constructor
  · have h := le_max_left
      (X.generator w y - q * w y) (1 - deriv w y)
    rw [hmax] at h
    exact h
  · have h := le_max_right
      (X.generator w y - q * w y) (1 - deriv w y)
    rw [hmax] at h
    linarith
