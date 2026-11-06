-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_finite_physical_grid_marked_count_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:36:20.368603+00:00
-- url     : https://prove2.me/submissions/0bc93e6e-cd76-4c0b-9222-fcd48b3a4aa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_halfopen_marked_count_lintegral_add

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Every original-compatible marked jump in a monotone finite physical grid
belongs to exactly one half-open cell, including at its right endpoint. -/
theorem solution
    (S : Set ℝ≥0) (hS : MeasurableSet S)
    (mark : ℝ≥0 → ℝ≥0 × ℝ) (hmark : Measurable mark)
    (F : ℝ≥0 × ℝ → ℝ≥0∞) (hF : Measurable F)
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ) :
    (∫⁻ p, F p ∂((Measure.count.restrict
      (S ∩ Set.Ioc (u 0) (u n))).map mark)) =
      ∑ i ∈ Finset.range n,
        (∫⁻ p, F p ∂((Measure.count.restrict
          (S ∩ Set.Ioc (u i) (u (i + 1)))).map mark)) := by
  induction n with
  | zero =>
      have hEmpty :
          S ∩ Set.Ioc (u 0) (u 0) = ∅ := by
        ext v
        simp
      simp [hEmpty]
  | succ n ih =>
      have h0n : u 0 ≤ u n := hmono (Nat.zero_le n)
      have hns : u n ≤ u (n + 1) := hmono (Nat.le_succ n)
      have hAdd :=
        avram_p3_2_halfopen_marked_count_lintegral_add
          S hS mark hmark F hF
          (u 0) (u n) (u (n + 1)) h0n hns
      simpa only [Nat.succ_eq_add_one, Finset.sum_range_succ, ih] using hAdd
