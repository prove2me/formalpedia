-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_payoff_zero_of_negative_initial_reserve
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T07:48:20.619781+00:00
-- url     : https://prove2.me/submissions/70dc7a52-f370-46cc-8035-b0240ec8e7a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (hx : x < 0) (W : ℝ → ℝ) (t : ℝ≥0) (ω : Ω) :
    ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
      (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω = 0 := by
  refine indicator_of_notMem (fun h => ?_) _
  have := h 0 bot_le
  rw [X.X_zero] at this
  linarith
