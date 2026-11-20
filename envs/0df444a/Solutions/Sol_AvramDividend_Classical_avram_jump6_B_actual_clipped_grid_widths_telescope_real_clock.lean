-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_actual_clipped_grid_widths_telescope_real_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:16:27.39571+00:00
-- url     : https://prove2.me/submissions/44e1e37c-d29c-4e36-8bb0-aa4ede726c81

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section
set_option autoImplicit false

theorem solution
    (n j : ℕ) (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0)) :
    let u : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    (∑ i ∈ Finset.range m,
      (((u (i + 1) - u i : ℝ≥0) : ℝ))) = (t : ℝ) := by
  let u : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
  let m : ℕ := (n + 1) * (j + 1)
  obtain ⟨hmono, hzero, hend⟩ :=
    avram_jump6_B_actual_canonical_grid_monotone_zero_and_reaches_stop_v2
      n j t ht
  have htel : ∀ k : ℕ,
      (∑ i ∈ Finset.range k, ((u (i + 1) : ℝ) - (u i : ℝ))) =
        (u k : ℝ) - (u 0 : ℝ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have hdiff (i : ℕ) :
      (((u (i + 1) - u i : ℝ≥0) : ℝ)) =
      (u (i + 1) : ℝ) - (u i : ℝ) := by
    have hh := tsub_add_cancel_of_le (hmono (Nat.le_succ i))
    have hr : (((u (i + 1) - u i : ℝ≥0) : ℝ)) + (u i : ℝ) =
        (u (i + 1) : ℝ) := by exact_mod_cast hh
    linarith
  change (∑ i ∈ Finset.range m,
      (((u (i + 1) - u i : ℝ≥0) : ℝ))) = (t : ℝ)
  calc
    (∑ i ∈ Finset.range m,
      (((u (i + 1) - u i : ℝ≥0) : ℝ))) =
      ∑ i ∈ Finset.range m,
        ((u (i + 1) : ℝ) - (u i : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hdiff i
    _ = (u m : ℝ) - (u 0 : ℝ) := htel m
    _ = (t : ℝ) := by
      change u 0 = 0 at hzero
      change u m = t at hend
      rw [hzero, hend]
      simp