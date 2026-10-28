-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_ordinary_deriv_zero_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:35:47.2571+00:00
-- url     : https://prove2.me/submissions/6e2b8e2b-febc-46d9-b8cf-3a32d4a0f232

import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The ordinary derivative vanishes at the nonnegative zero boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0) :
    deriv W 0 = 0 := by
  have hnonneg : ∀ y : ℝ, 0 ≤ W y := by
    intro y
    by_cases hy : y < 0
    · rw [hW.1 y hy]
    · exact hW.2.1 y (le_of_not_gt hy)
  have hmin : IsLocalMin W 0 := by
    apply Filter.Eventually.of_forall
    intro y
    rw [hzero]
    exact hnonneg y
  exact hmin.deriv_eq_zero
