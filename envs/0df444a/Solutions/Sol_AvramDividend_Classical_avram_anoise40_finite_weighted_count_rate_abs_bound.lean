-- Prove2me | solution 1 for AvramDividend.Classical.avram_anoise40_finite_weighted_count_rate_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:54:24.915196+00:00
-- url     : https://prove2.me/submissions/2ecf22f6-8176-415d-9452-342f72227b6c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

/-- Unit-weight signed compensation is bounded by total counts and rates. -/
theorem solution
    {ι : Type*} (S : Finset ι)
    (w a b : ι → ℝ)
    (hw : ∀ i ∈ S, |w i| ≤ 1)
    (ha : ∀ i ∈ S, 0 ≤ a i)
    (hb : ∀ i ∈ S, 0 ≤ b i) :
    |∑ i ∈ S, w i * (a i - b i)| ≤
      (∑ i ∈ S, a i) + (∑ i ∈ S, b i) := by
  classical
  calc
    |∑ i ∈ S, w i * (a i - b i)| ≤
        ∑ i ∈ S, |w i * (a i - b i)| :=
      Finset.abs_sum_le_sum_abs (fun i => w i * (a i - b i)) S
    _ ≤ ∑ i ∈ S, (a i + b i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hdiff : |a i - b i| ≤ a i + b i := by
        apply abs_le.mpr
        constructor <;> linarith [ha i hi, hb i hi]
      calc
        |w i * (a i - b i)| = |w i| * |a i - b i| := abs_mul _ _
        _ ≤ 1 * (a i + b i) :=
          mul_le_mul (hw i hi) hdiff (abs_nonneg _) (by norm_num)
        _ = a i + b i := one_mul _
    _ = (∑ i ∈ S, a i) + (∑ i ∈ S, b i) :=
      Finset.sum_add_distrib
