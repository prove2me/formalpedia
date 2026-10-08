-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:43:55.817634+00:00
-- url     : https://prove2.me/submissions/5e8f6886-1d83-42e5-9f0a-a40fbf39dcf8

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
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    Monotone W := by
  rcases hW with ⟨hneg, hnonneg, hcont, hmono, hlap⟩
  intro x y hxy
  by_cases hy0 : y < 0
  · have hx0 : x < 0 := lt_of_le_of_lt hxy hy0
    rw [hneg x hx0, hneg y hy0]
  · have hy_nonneg : 0 ≤ y := le_of_not_gt hy0
    by_cases hx0 : x < 0
    · rw [hneg x hx0]
      exact hnonneg y hy_nonneg
    · have hx_nonneg : 0 ≤ x := le_of_not_gt hx0
      exact hmono hx_nonneg hy_nonneg hxy
