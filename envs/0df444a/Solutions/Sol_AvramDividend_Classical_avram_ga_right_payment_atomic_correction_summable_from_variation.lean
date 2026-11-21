-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_right_payment_atomic_correction_summable_from_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:40:18.165239+00:00
-- url     : https://prove2.me/submissions/7ebaec19-7ee9-4ba6-bd24-df898e04c3a9

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.SetSemiring
open MeasureTheory
noncomputable section

theorem solution
    {ι : Type*} (V : ℝ → ℝ) (Y J E : ι → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hJ : ∀ i, 0 ≤ J i)
    (hJsum : Summable J)
    (hE : ∀ i, 0 ≤ E i ∧ E i ≤ 1)
    (hV : ∀ i, |V (Y i - J i) - V (Y i)| ≤ L * J i) :
    Summable (fun i => E i * (V (Y i - J i) - V (Y i) + J i)) := by
  have hDom : Summable (fun i => (L + 1) * J i) :=
    hJsum.mul_left (L + 1)
  apply Summable.of_norm_bounded hDom
  intro i
  have hj := hJ i
  have he := hE i
  have hv := hV i
  have hC : |V (Y i - J i) - V (Y i) + J i| ≤ (L + 1) * J i := by
    calc
      _ ≤ |V (Y i - J i) - V (Y i)| + |J i| := abs_add_le _ _
      _ ≤ L * J i + J i := by
        rw [abs_of_nonneg hj]
        linarith
      _ = (L + 1) * J i := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he.1]
  have hbound : 0 ≤ (L + 1) * J i := mul_nonneg (by linarith) hj
  nlinarith [abs_nonneg (V (Y i - J i) - V (Y i) + J i)]
