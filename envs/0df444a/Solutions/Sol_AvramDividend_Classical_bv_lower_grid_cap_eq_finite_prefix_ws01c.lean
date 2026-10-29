-- Prove2me | solution 1 for AvramDividend.Classical.bv_lower_grid_cap_eq_finite_prefix_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:02:53.514012+00:00
-- url     : https://prove2.me/submissions/8a873514-b622-497c-8df2-c8b4b8974d4d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_capped_iInf_finite_prefix_ws01c

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set Order AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (Y : ℝ≥0 → ℝ) (lower : ℝ)
    (h T : ℝ≥0) (hh : 0 < h) (M : ℕ)
    (hCover : T ≤ (M : ℝ≥0) * h) :
    ((⨅ k : ℕ,
      if Y ((k : ℝ≥0) * h) < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ⊓ (T : ℝ≥0∞)) =
    ((⨅ (k : ℕ) (_ : k ≤ M),
      if Y ((k : ℝ≥0) * h) < lower then
        (((k : ℝ≥0) * h) : ℝ≥0∞) else ∞) ⊓ (T : ℝ≥0∞)) := by
  apply bv_capped_iInf_finite_prefix_ws01c
  intro k hk
  have hkNN : (M : ℝ≥0) ≤ (k : ℝ≥0) := by
    exact_mod_cast Nat.le_of_lt hk
  have hGrid : T ≤ (k : ℝ≥0) * h :=
    hCover.trans (mul_le_mul_of_nonneg_right hkNN (by positivity))
  split_ifs with hcross
  · exact_mod_cast hGrid
  · exact le_top