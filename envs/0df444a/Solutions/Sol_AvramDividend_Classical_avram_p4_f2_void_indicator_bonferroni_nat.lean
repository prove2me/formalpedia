-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f2_void_indicator_bonferroni_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:25:53.009798+00:00
-- url     : https://prove2.me/submissions/695b5ae0-a08a-42ce-a650-fa77e84b557b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The first two factorial terms sandwich the indicator of a nonempty count. -/
theorem solution (k : ℕ) :
    (k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2 ≤
      (if k = 0 then 0 else (1 : ℝ)) ∧
    (if k = 0 then 0 else (1 : ℝ)) ≤ (k : ℝ) := by
  constructor
  · by_cases hk0 : k = 0
    · subst k
      norm_num
    · by_cases hk1 : k = 1
      · subst k
        norm_num
      · have hk2 : 2 ≤ k := by omega
        have hk2r : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
        have hprod : 0 ≤ ((k : ℝ) - 1) * ((k : ℝ) - 2) :=
          mul_nonneg (by linarith) (by linarith)
        simp [hk0]
        nlinarith
  · by_cases hk0 : k = 0
    · subst k
      norm_num
    · simp [hk0]
      have hk1 : 1 ≤ k := by omega
      exact_mod_cast hk1
