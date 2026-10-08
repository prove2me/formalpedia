-- Prove2me | solution 1 for AvramDividend.Classical.monotone_integer_growth_to_real_eventual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:34:20.995359+00:00
-- url     : https://prove2.me/submissions/604e0c53-af7f-488a-a577-c65d852bba05

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

theorem solution
    (f : ℝ → ℝ) (hf : Monotone f)
    (hlim : Filter.Tendsto (fun n : ℕ => f ((n : ℝ) + 1))
        Filter.atTop Filter.atTop)
    (B : ℝ) :
    ∃ θ₀ : ℝ, ∀ θ : ℝ, θ₀ ≤ θ → B < f θ := by
  have hev : ∀ᶠ n : ℕ in atTop, B < f ((n : ℝ) + 1) :=
    hlim.eventually (Ioi_mem_atTop B)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  refine ⟨(N : ℝ) + 1, ?_⟩
  intro θ hθ
  exact lt_of_lt_of_le (hN N le_rfl) (hf hθ)
