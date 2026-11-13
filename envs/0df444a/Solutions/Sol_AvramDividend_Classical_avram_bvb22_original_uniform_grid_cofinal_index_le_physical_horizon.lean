-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_original_uniform_grid_cofinal_index_le_physical_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:47:58.342332+00:00
-- url     : https://prove2.me/submissions/6de519e2-ae9b-4f59-b26d-62837baa1f86

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (n i : ℕ) (hi : i ≤ n + 1) :
    u n i ≤ (⟨T, hT⟩ : ℝ≥0) := by
  apply Subtype.coe_le_coe.mp
  change (u n i : ℝ) ≤ T
  rw [huniform n i]
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  apply (div_le_iff₀ hn).2
  have hcast : (i : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hi
  nlinarith [mul_nonneg hT (sub_nonneg.mpr hcast)]
