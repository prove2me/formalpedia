-- Prove2me | solution 1 for AvramDividend.Classical.zero_reflectedSupValue_of_ae_instant_ruin_and_W_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:17:12.2988+00:00
-- url     : https://prove2.me/submissions/2488d622-c421-41ff-b91f-ff874ec59324

import Theorems.Thm_AvramDividend_Classical_barrierSupValue_zero_of_ae_instant_ruin
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_of_scale_origin_zero
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Combine zero stopped reward with the zero scale-function origin value. -/
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
