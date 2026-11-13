-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb22_zero_contact_cell_budget_finset_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:01:09.386114+00:00
-- url     : https://prove2.me/submissions/fbaf0a61-9434-4421-95ff-51cc0b309838

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q rate w0 : ℝ) (hq : 0 < q) (hrate : 0 ≤ rate)
    (hw0 : 0 ≤ w0) (u : ℕ → ℝ) (hu : Monotone u)
    (cash : ℕ → ℝ)
    (hCash : ∀ i : ℕ, cash i ≤ (q + rate) * w0 *
      ((Real.exp (-(q * u i)) - Real.exp (-(q * u (i + 1)))) / q))
    (n : ℕ) :
    (∑ i ∈ Finset.range n, cash i) +
      Real.exp (-(q * u n)) * w0 -
      Real.exp (-(q * u 0)) * w0 ≤
      ∑ i ∈ Finset.range n,
        rate * w0 * Real.exp (-(q * u i)) * (u (i + 1) - u i) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hst : u n ≤ u (n + 1) := hu (Nat.le_succ n)
      have hcell :=
        avram_bv_excess20_original_zero_cell_discount_compensator_ceiling
          q rate w0 (cash n) (u n) (u (n + 1))
          hq hrate hw0 hst (hCash n)
      simp only [Finset.sum_range_succ]
      linarith
