-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_h_cadlag_eventually_nonzero_test_grid_count_le_large_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:32:02.278243+00:00
-- url     : https://prove2.me/submissions/aee136be-a0e3-4877-9c28-0b752671e25b

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
import Theorems.Thm_AvramDividend_Classical_avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology AvramDividend.Classical
open scoped NNReal BigOperators

/-- Every sufficiently fine nonzero test increment is assigned to an
actual large jump, giving an eventual deterministic grid count bound. -/
theorem solution
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0) (hT : 0 < T)
    (ρ : ℝ) (hρ : 0 < ρ) (f : ℝ → ℝ)
    (hfzero : ∀ z : ℝ, |z| < ρ → f z = 0)
    (S : Finset ℝ≥0)
    (hS : ∀ t : ℝ≥0, 0 < t → t ≤ T →
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ S)
    (j : ℝ≥0 → ℕ → ℕ)
    (hj : ∀ u ∈ S, ∀ n : ℕ,
      j u n ≤ n ∧
      (j u n : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ (((j u n + 1 : ℕ) : ℝ≥0) *
        (T / ((n : ℝ≥0) + 1))))
    (hL : ∀ t, t ≤ T →
      Tendsto Y (𝓝[<] t) (𝓝 (Function.leftLim Y t)))
    (hR : ∀ t, t ≤ T → ContinuousWithinAt Y (Ici t) t) :
    ∀ᶠ n : ℕ in atTop,
      ((Finset.range (n + 1)).filter (fun i =>
        f (Y (((i + 1 : ℕ) : ℝ≥0) *
          (T / ((n : ℝ≥0) + 1))) -
          Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))) ≠ 0)).card ≤ S.card := by
  have hz :=
    avram_p2_h_cadlag_uniform_test_zero_outside_all_large_jump_cells
      Y T hT ρ hρ f hfzero S hS j hj hL hR
  filter_upwards [hz] with n hn
  exact avram_p2_h_cadlag_finite_nonzero_grid_cells_count_le_selected_jumps
    S (fun u => j u n) n
    (fun i => f (Y (((i + 1 : ℕ) : ℝ≥0) *
      (T / ((n : ℝ≥0) + 1))) -
      Y ((i : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))) hn
