-- Prove2me | solution 1 for AvramDividend.Classical.bv_standing_drift_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:08:15.221991+00:00
-- url     : https://prove2.me/submissions/c8ecf0f5-2bac-4ca3-8df5-7168185a5fcd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hstanding : X.Standing) (hBV : X.BoundedVariation) :
    0 < X.drift ∧ X.ν ≠ 0 := by
  have hn : ¬ (X.drift ≤ 0 ∨ X.ν = 0) := by
    intro h
    exact hstanding.1 ⟨hBV, h⟩
  constructor
  · exact lt_of_not_ge (fun h => hn (Or.inl h))
  · exact fun h => hn (Or.inr h)
