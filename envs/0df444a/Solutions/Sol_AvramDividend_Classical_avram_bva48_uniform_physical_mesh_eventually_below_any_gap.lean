-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva48_uniform_physical_mesh_eventually_below_any_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:09:23.864138+00:00
-- url     : https://prove2.me/submissions/493873a5-0558-4346-a76e-678b76b0192e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter

/-- The source-exact uniform physical mesh is eventually below every positive gap. -/
theorem solution (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, T / ((n : ℝ) + 2) < δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hlim : T / δ < (n : ℝ) + 2 := by linarith
  apply (div_lt_iff₀ hden).2
  nlinarith [(div_lt_iff₀ hδ).1 hlim]
