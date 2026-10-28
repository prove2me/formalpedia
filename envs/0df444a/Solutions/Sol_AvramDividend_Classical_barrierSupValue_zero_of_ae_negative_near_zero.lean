-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_zero_of_ae_negative_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T21:39:59.444921+00:00
-- url     : https://prove2.me/submissions/66ed14dc-f306-4b5a-aa57-9b61b6c22ab2

import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_of_near_zero_negative_path
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Almost-sure early negative paths give a zero stopped reflected dividend reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    barrierSupValue X 0 q = 0 := by
  have hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0 :=
    hNear.mono (fun ω hω =>
      barrierRuinTime_zero_of_near_zero_negative_path X ω hω)
  exact barrierSupValue_zero_of_ae_instant_ruin X 0 q hRuin
