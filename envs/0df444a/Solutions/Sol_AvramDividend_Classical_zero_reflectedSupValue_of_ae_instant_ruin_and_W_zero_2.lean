-- Prove2me | solution 2 for AvramDividend.Classical.zero_reflectedSupValue_of_ae_instant_ruin_and_W_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:18:30.974726+00:00
-- url     : https://prove2.me/submissions/82e3ebcc-21d4-4d8f-9c3c-5c537ee66196

import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_origin_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Instant zero-barrier ruin and a vanishing scale origin force zero reflected value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hRuin : ∀ᵐ ω ∂P, barrierRuinTime X 0 ω = 0)
    (hW0 : W 0 = 0) :
    barrierSupValue X 0 q = ENNReal.ofReal (barrierValue W 0 0) := by 
  rw [barrierSupValue_zero_of_ae_instant_ruin X 0 q hRuin,
    barrierValue_zero_of_scale_origin_zero W hW0]
  simp
