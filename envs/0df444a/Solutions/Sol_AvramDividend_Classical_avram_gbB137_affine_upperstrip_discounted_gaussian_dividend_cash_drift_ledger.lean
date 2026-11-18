-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB137_affine_upperstrip_discounted_gaussian_dividend_cash_drift_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:51:38.83129+00:00
-- url     : https://prove2.me/submissions/a0ab22d2-2906-460f-a9fc-1e9915233f0c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- The affine caplinear upper branch leaves an explicit positive drift cash source. -/
theorem solution
    (m : ℕ) (a B s D : ℕ → ℝ) (C κ : ℝ) :
    let Y : ℕ → ℝ := fun i => C + B i + 2 * s i - D i
    a m * (Y (m + 1) + κ) +
      (Finset.range (m + 1)).sum (fun i => a i * (D (i + 1) - D i)) -
      a 0 * (Y 0 + κ) -
      (Finset.range (m + 1)).sum (fun i => a i * (B (i + 1) - B i)) =
    2 * (Finset.range (m + 1)).sum (fun i => a i * (s (i + 1) - s i)) -
      (Finset.range m).sum (fun i => (a i - a (i + 1)) * Y (i + 1)) +
      (a m - a 0) * κ := by
  let w : ℝ → ℝ := fun y => y + κ
  have h := avram_gbB57_original_gaussian_finite_discounted_cash_abel_ledger
    m a B s D C w
  dsimp [w] at h
  dsimp
  convert h using 1 <;> ring
