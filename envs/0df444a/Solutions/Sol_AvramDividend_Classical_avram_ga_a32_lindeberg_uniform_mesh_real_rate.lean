-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a32_lindeberg_uniform_mesh_real_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:26:53.237359+00:00
-- url     : https://prove2.me/submissions/90f27ff5-0a27-4c6c-9ea6-e031fdfa77cd

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- The deterministic fourth-moment mesh rate is O(1/(m+1)).
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (n m : ℕ) :
    (∑ _i ∈ Finset.range m,
      (3 : ℝ) * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2) ≤
      3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hratio : (m : ℝ) / ((m : ℝ) + 1) ≤ 1 :=
    (div_le_iff₀ hpos).2 (by linarith)
  have hsq : 0 ≤ (3 : ℝ) * (n : ℝ) ^ 2 := by positivity
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have heq :
      (m : ℝ) * (3 * ((n : ℝ) / ((m : ℝ) + 1)) ^ 2) =
        ((m : ℝ) / ((m : ℝ) + 1)) *
          (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) := by
    field_simp
  rw [heq]
  nlinarith [div_nonneg hsq (le_of_lt hpos)]
