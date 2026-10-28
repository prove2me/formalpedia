-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_zero_le_scale_ratio_of_positive_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:15:37.998623+00:00
-- url     : https://prove2.me/submissions/d84fe6ff-d11d-425e-a6b0-e5a9f4f87513

import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine zero-barrier stopped regulator reward is bounded by any
positive-barrier scale ratio once that positive-barrier identity is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hpositive : ∀ a : ℝ, 0 < a →
      barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a)) :
    ∀ a : ℝ, 0 < a →
      barrierSupValue X 0 q ≤ ENNReal.ofReal (W a / deriv W a) := by
  intro a ha
  rw [← hpositive a ha]
  exact barrierSupValue_mono_barrier X 0 a q (le_of_lt ha)
