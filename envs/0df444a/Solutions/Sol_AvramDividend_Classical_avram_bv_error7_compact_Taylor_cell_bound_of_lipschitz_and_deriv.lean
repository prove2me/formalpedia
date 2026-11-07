-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:37:18.780724+00:00
-- url     : https://prove2.me/submissions/803da167-3742-4c01-a148-1f6df2f26969

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A compact-band Lipschitz bound for w and a derivative bound give
a global linear Taylor-error envelope, without assuming a small cell. -/
theorem solution
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (y d : ℝ)
    (hCell : Set.uIcc y (y + d) ⊆ Set.Icc a b) :
    |w (y + d) - w y - deriv w y * d| ≤ (2 * L) * |d| := by
  have hy : y ∈ Set.Icc a b := hCell Set.left_mem_uIcc
  have hz : y + d ∈ Set.Icc a b := hCell Set.right_mem_uIcc
  have hw := hLip y hy (y + d) hz
  have hdiff : (y + d) - y = d := by ring
  rw [hdiff] at hw
  have hd := hDeriv y hy
  have hmul : |deriv w y * d| ≤ L * |d| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hd (abs_nonneg d)
  calc
    |w (y + d) - w y - deriv w y * d|
        ≤ |w (y + d) - w y| + |deriv w y * d| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le (w (y + d) - w y) (-(deriv w y * d)))
    _ ≤ L * |d| + L * |d| := add_le_add hw hmul
    _ = (2 * L) * |d| := by ring
