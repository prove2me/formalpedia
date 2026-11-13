-- Prove2me | solution 2 for AvramDividend.Classical.avram_ga_a54_original_uniform_gaussian_unique_stop_crossing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:24:28.430613+00:00
-- url     : https://prove2.me/submissions/9ea539e6-8a95-43c7-89c9-be1985bbe336

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger163_true_uniform_clipped_mesh_first_crossing
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- The genuine m+1 clipped Gaussian grid crosses the positive stop exactly once. -/
theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (hρn : ρ ≤ (n : ℝ≥0))
    (hρpos : 0 < ρ) (hm : 0 < m) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    ∃ k : ℕ, k < m + 1 ∧ v k < ρ ∧ v (k + 1) = ρ ∧
      (∀ i : ℕ, i < k → v (i + 1) < ρ) ∧
      (∀ i : ℕ, k < i → v i = ρ) := by
  have hn : 0 < n := by
    have hp : (0 : ℝ≥0) < (n : ℝ≥0) := lt_of_lt_of_le hρpos hρn
    exact_mod_cast hp
  exact avram_gledger163_true_uniform_clipped_mesh_first_crossing
    n m hn ρ hρn hρpos
