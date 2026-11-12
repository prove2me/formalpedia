-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva49_original_uniform_grid_isolates_finite_jump_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:12:53.840855+00:00
-- url     : https://prove2.me/submissions/b029b33a-e5d5-4a34-958f-3f900b55a4c4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva41_finite_distinct_mark_times_positive_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical

/-- Every sufficiently fine source-exact uniform time cell isolates its finite jump marks. -/
theorem solution (S : Finset ℝ) (T : ℝ) (hT : 0 < T) :
    ∀ᶠ n : ℕ in atTop, ∀ a s t : ℝ,
      s ∈ S → t ∈ S →
      a ≤ s → s < a + T / ((n : ℝ) + 2) →
      a ≤ t → t < a + T / ((n : ℝ) + 2) → s = t := by
  obtain ⟨δ, hδ, hsep⟩ := avram_bva41_finite_distinct_mark_times_positive_gap S
  obtain ⟨N, hN⟩ := exists_nat_gt (T / δ)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n : ℝ) + 2 := by positivity
  have hlim : T / δ < (n : ℝ) + 2 := by linarith
  have hmesh : T / ((n : ℝ) + 2) < δ := by
    apply (div_lt_iff₀ hden).2
    nlinarith [(div_lt_iff₀ hδ).1 hlim]
  intro a s t hs ht has hsm hat htm
  by_contra hne
  have hgap := hsep s hs t ht hne
  have hshort : |s - t| < T / ((n : ℝ) + 2) := by
    apply abs_lt.mpr
    constructor <;> linarith
  linarith
