-- Prove2me | solution 1 for AvramDividend.Classical.positive_atom_geometric_measure_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T21:37:06.882991+00:00
-- url     : https://prove2.me/submissions/cbe6d14d-49e1-4b98-ada0-f9ac1e5addc6

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : ℕ → Measure α) (c : ℝ≥0∞) (hc : 0 < c) (x : α)
    (hm0 : m 0 = Measure.dirac x) :
    0 < (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) {x} := by
  have hle :
      (c ^ (0 + 1) • m 0) {x} ≤
        (Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)) {x} := by
    exact Measure.le_sum (fun n : ℕ => c ^ (n + 1) • m n) 0 {x}
  have hterm : (c ^ (0 + 1) • m 0) {x} = c := by
    simp [hm0]
  rw [hterm] at hle
  exact hc.trans_le hle
