-- Prove2me | solution 1 for AvramDividend.Classical.ae_negative_near_zero_of_absolutelyContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:50:58.627118+00:00
-- url     : https://prove2.me/submissions/2d1cad79-3813-44ee-a020-0c414642173b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P Q : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hAC : Q ≪ P)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X t ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X t ω < 0 := by
  exact Filter.Eventually.filter_mono hAC.ae_le hRegP
