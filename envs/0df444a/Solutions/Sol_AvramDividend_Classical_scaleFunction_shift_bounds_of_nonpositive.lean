-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_shift_bounds_of_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:30:43.596904+00:00
-- url     : https://prove2.me/submissions/42fc4fdc-e2d7-4879-b9d5-90c7e577e6c6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0) :
    0 ≤ W (x + y) ∧ W (x + y) ≤ W x := by
  rcases hW with ⟨hneg, hnonneg, hcont, hmono, hlap⟩
  by_cases hxy : x + y < 0
  · have hwxy : W (x + y) = 0 := hneg (x + y) hxy
    constructor
    · rw [hwxy]
    · rw [hwxy]
      exact hnonneg x hx
  · have hxy0 : 0 ≤ x + y := le_of_not_gt hxy
    have hle : x + y ≤ x := by linarith
    constructor
    · exact hnonneg (x + y) hxy0
    · exact hmono hxy0 hx hle
