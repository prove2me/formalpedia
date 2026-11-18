-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_exponential_pgf_count_cell_coefficients_mecke_recurrence_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:11:24.520301+00:00
-- url     : https://prove2.me/submissions/a802b701-eb70-4b0d-a373-75579bc80669

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped BigOperators
noncomputable section
theorem solution
    (C : ℕ → ℝ) (r q : ℝ)
    (hSeries : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k : ℕ => z ^ k * C k) (Real.exp (q * z - r))) :
    ∀ k : ℕ, (((k + 1 : ℕ) : ℝ) * C (k + 1)) = q * C k := by
  have hC :=
    avram_a27_real_exponential_pgf_hasSum_unique_power_series_coefficients_20261117
      C r q hSeries
  intro k
  rw [hC (k + 1), hC k]
  have hk : (k.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (((k + 1).factorial : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k + 1)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
