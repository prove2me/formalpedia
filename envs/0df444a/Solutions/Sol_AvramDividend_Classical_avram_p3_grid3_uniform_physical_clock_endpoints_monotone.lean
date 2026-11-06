-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid3_uniform_physical_clock_endpoints_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:53:17.756211+00:00
-- url     : https://prove2.me/submissions/1bd86398-fb28-41cd-a081-b4241516b255

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ≥0) (m : ℕ) :
    let u : ℕ → ℝ≥0 := fun i =>
      ((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))
    u 0 = 0 ∧ u (m + 1) = T ∧ Monotone u := by
  refine ⟨?_, ?_, ?_⟩
  · simp
  · change ((min (m + 1) (m + 1) : ℕ) : ℝ≥0) *
      (T / (m + 1 : ℝ≥0)) = T
    simp only [min_self]
    have hm : (m + 1 : ℝ≥0) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    field_simp [hm]
    simp only [Nat.cast_add, Nat.cast_one] <;> ring
  · intro i j hij
    change ((min i (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1 : ℝ≥0)) ≤
      ((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1 : ℝ≥0))
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast min_le_min_right (m + 1) hij
    · positivity
