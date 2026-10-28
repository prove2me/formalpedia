-- Prove2me | solution 1 for AvramDividend.Classical.geometric_measure_sum_extract_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:12:27.958994+00:00
-- url     : https://prove2.me/submissions/0b8ecd3f-91d9-4af1-8bab-e3ee535d9aa5

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal

/-- Factor a geometric coefficient out of a countable sum of positive measures. -/
theorem solution (c : ℝ≥0∞) (m : ℕ → Measure ℝ) :
    Measure.sum (fun n : ℕ => c ^ (n + 1) • m n) =
      c • Measure.sum (fun n : ℕ => c ^ n • m n) := by
  apply Measure.ext
  intro s hs
  rw [Measure.sum_apply _ hs, Measure.smul_apply, Measure.sum_apply _ hs]
  simp only [Measure.smul_apply, pow_succ]
  calc
    (∑' n : ℕ, (c ^ n * c) * (m n) s) =
      ∑' n : ℕ, c * (c ^ n * (m n) s) := by
        congr 1
        funext n
        ac_rfl
    _ = c * ∑' n : ℕ, c ^ n * (m n) s :=
      ENNReal.tsum_mul_left
