-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_prescribed_uniform_physical_grid_is_monotone_and_has_exact_last_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:30:44.65546+00:00
-- url     : https://prove2.me/submissions/31f23ba3-fa7e-47ab-9851-37eefb0a484c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical
open scoped NNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hu0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    (∀ n, u n 0 = 0 ∧
      (u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2)) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) := by
  constructor
  · intro n
    refine ⟨hu0 n, ?_⟩
    rw [huniform n (n + 1)]
    have hd : (n : ℝ) + 2 ≠ 0 := by positivity
    push_cast
    field_simp [hd]
    ring
  · intro n i hi
    apply NNReal.coe_le_coe.mp
    rw [huniform n i, huniform n (i + 1)]
    have hd : 0 < (n : ℝ) + 2 := by positivity
    apply (div_le_div_iff_of_pos_right hd).2
    have hi' : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ i
    exact mul_le_mul_of_nonneg_left hi' (le_of_lt hT)
