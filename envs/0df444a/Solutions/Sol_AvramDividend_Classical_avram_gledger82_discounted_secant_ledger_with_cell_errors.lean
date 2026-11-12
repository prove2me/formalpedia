-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger82_discounted_secant_ledger_with_cell_errors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:08:00.032547+00:00
-- url     : https://prove2.me/submissions/7da80170-cef9-4a2e-aed2-4a8e6102528d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section

theorem solution
    (w : ℝ → ℝ) (u preDividend cash err : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)) + err k)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) +
        Real.exp (-(q * s n)) * w (u n) ≤
      w (u 0) +
        ∑ k ∈ Finset.range n,
          (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
            Real.exp (-(q * s k)) * w (u k)) +
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * err k := by
  have hc (k : ℕ) : cash k - err k ≤ w (preDividend k) - w (u (k + 1)) := by
    linarith [hCash k]
  have h := discounted_finite_grid_levy_dividend_secant_ledger
    w u preDividend (fun k => cash k - err k) s q hs0 hc n
  have hsum :
      (∑ k ∈ Finset.range n,
        Real.exp (-(q * s (k + 1))) * (cash k - err k)) =
      (∑ k ∈ Finset.range n,
        Real.exp (-(q * s (k + 1))) * cash k) -
      (∑ k ∈ Finset.range n,
        Real.exp (-(q * s (k + 1))) * err k) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at h
  linarith
