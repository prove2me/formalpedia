-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_count_nonfinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:52:43.24984+00:00
-- url     : https://prove2.me/submissions/b4ea813b-9788-4246-bc40-71173c1fbce2

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_weighted_series_not_summable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A weighted singular source-cell loss has infinite counting absolute integral. -/
theorem solution (y : Nat -> Real)
    (hy : forall k, 0 < y k)
    (hsmall : forall k, y k <= 1 / 16)
    (hpower : forall k, y k <= 1 / ((2 : Real) ^ k) ^ 2) :
    Not (MeasureTheory.HasFiniteIntegral (fun k : Nat =>
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k) MeasureTheory.Measure.count) := by
  intro hfi
  have hnorm : Summable (fun k : Nat =>
      ‖(-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k‖) :=
    (MeasureTheory.hasFiniteIntegral_count_iff).1 hfi
  have hsum : Summable (fun k : Nat =>
      (-(3 + y k - 4 * Real.sqrt (y k) - 2 / Real.sqrt (y k))) /
        (2 : Real) ^ k) :=
    (summable_norm_iff).1 hnorm
  exact (AvramDividend.Classical.avram_a19_singular_weighted_series_not_summable
    y hy hsmall hpower) hsum
