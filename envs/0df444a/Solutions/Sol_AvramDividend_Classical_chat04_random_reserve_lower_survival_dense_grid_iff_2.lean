-- Prove2me | solution 2 for AvramDividend.Classical.chat04_random_reserve_lower_survival_dense_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:44:16.096085+00:00
-- url     : https://prove2.me/submissions/9daa53d5-c348-45c7-a683-4051cbeea06e

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t < T → 0 ≤ H ω + X.X t ω) ↔
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by
  have h := AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff X ω (-H ω) T
  constructor
  · intro hall n hn k hk
    by_contra hc
    push_neg at hc
    obtain ⟨s, hs, hX⟩ := h.2 ⟨n, hn, k, hk, by linarith⟩
    have := hall s hs
    linarith
  · intro hall t ht
    by_contra hc
    push_neg at hc
    obtain ⟨n, hn, k, hk, hX⟩ := h.1 ⟨t, ht, by linarith⟩
    have := hall n hn k hk
    linarith
