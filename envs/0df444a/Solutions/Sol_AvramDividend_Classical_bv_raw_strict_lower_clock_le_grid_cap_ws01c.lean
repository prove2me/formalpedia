-- Prove2me | solution 1 for AvramDividend.Classical.bv_raw_strict_lower_clock_le_grid_cap_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T22:56:25.594985+00:00
-- url     : https://prove2.me/submissions/f619fd7a-4e12-4495-9d84-deb6bea4fa23

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

theorem solution
    (Y : ℝ≥0 → ℝ) (lower : ℝ)
    (h T : ℝ≥0) (M : ℕ) :
    ((⨅ (t : ℝ≥0) (_ : Y t < lower), (t : ℝ≥0∞)) ⊓
      (T : ℝ≥0∞)) ≤
    ((⨅ (k : ℕ) (_ : k ≤ M),
        if Y ((k : ℝ≥0) * h) < lower then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ⊤) ⊓
        (T : ℝ≥0∞)) := by
  have hRawLe :
      (⨅ (t : ℝ≥0) (_ : Y t < lower), (t : ℝ≥0∞)) ≤
      (⨅ (k : ℕ) (_ : k ≤ M),
        if Y ((k : ℝ≥0) * h) < lower then
          (((k : ℝ≥0) * h) : ℝ≥0∞) else ⊤) := by
    refine le_iInf (fun k => le_iInf (fun hk => ?_))
    by_cases hCross : Y ((k : ℝ≥0) * h) < lower
    · simpa only [if_pos hCross] using
        ((iInf_le
          (fun t : ℝ≥0 => ⨅ (_ : Y t < lower),
            (t : ℝ≥0∞))
          ((k : ℝ≥0) * h)).trans
          (iInf_le
            (fun _ : Y ((k : ℝ≥0) * h) < lower =>
              (((k : ℝ≥0) * h) : ℝ≥0∞)) hCross))
    · simp only [if_neg hCross]
      exact le_top
  exact inf_le_inf hRawLe le_rfl
