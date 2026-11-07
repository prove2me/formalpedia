-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_strict6_diagonal_nonnegative_error_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:47:52.066965+00:00
-- url     : https://prove2.me/submissions/cc23d02f-9118-4de9-8fb6-b70907654353

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_diagonal_refinement
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter AvramDividend.Classical
open scoped Topology
noncomputable section

/-- Turn row-wise expected source-error convergence into one vanishing diagonal. -/
theorem solution
    (E : ℕ → ℕ → ℝ)
    (hnonneg : ∀ k n, 0 ≤ E k n)
    (hvanish : ∀ k, Tendsto (fun n => E k n) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ,
      (∀ k, k ≤ φ k) ∧
      Tendsto (fun k => E k (φ k)) atTop (𝓝 0) := by
  obtain ⟨φ, hφge, hφerr⟩ :=
    avram_bv_strict6_diagonal_refinement E hvanish
  refine ⟨φ, hφge, ?_⟩
  have hUpper : Tendsto
      (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1))
      atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  apply Filter.Tendsto.squeeze tendsto_const_nhds hUpper
  · intro k
    exact hnonneg k (φ k)
  · intro k
    exact (le_abs_self (E k (φ k))).trans (le_of_lt (hφerr k))
