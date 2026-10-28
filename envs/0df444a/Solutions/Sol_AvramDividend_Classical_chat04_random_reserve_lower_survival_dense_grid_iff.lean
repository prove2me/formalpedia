-- Prove2me | solution 1 for AvramDividend.Classical.chat04_random_reserve_lower_survival_dense_grid_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:43:40.180048+00:00
-- url     : https://prove2.me/submissions/e08cf3a2-965c-4389-9dd5-1fa5057d52e0

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Open-horizon lower survival for a random reserve is grid-detectable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t < T → 0 ≤ H ω + X.X t ω) ↔
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by
  constructor
  · intro h n hn k hkt
    exact h _ hkt
  · intro hg t ht
    by_contra hnot
    have hlt : X.X t ω < -(H ω) := by
      have hneg : H ω + X.X t ω < 0 := lt_of_not_ge hnot
      linarith
    rcases (chat03_lower_before_horizon_countable_grid_iff
      X ω (-(H ω)) T).mp ⟨t, ht, hlt⟩ with
      ⟨n, hn, k, hkt, hk⟩
    have hgood := hg n hn k hkt
    linarith
