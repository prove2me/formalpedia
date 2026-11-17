-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_masked_bounded_hessian_finite_sum_absolute_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:00:38.890196+00:00
-- url     : https://prove2.me/submissions/5106c1f8-e516-4b09-be2b-c24a1aabbb54

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Theorems.Thm_AvramDividend_Classical_avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
theorem solution
    (S : Finset ℕ) (cut : ℕ → Prop) [DecidablePred cut]
    (H R : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ i ∈ S, cut i → |H i| ≤ K) :
    |∑ i ∈ S, if cut i then H i / 2 * R i else 0| ≤
      (K / 2) * (∑ i ∈ S, if cut i then |R i| else 0) := by
  classical
  let hf : ℕ → ℝ := fun i => if cut i then H i else 0
  let rf : ℕ → ℝ := fun i => if cut i then R i else 0
  have hhf : ∀ i ∈ S, |hf i| ≤ K := by
    intro i hi
    by_cases h : cut i
    · simpa [hf, h] using hH i hi h
    · simpa [hf, h] using hK
  have hSum := avram_ga_a88_original_gaussian_bounded_discounted_hessian_cross_sum_le_source_energy
    S hf rf K hK hhf
  have heq : (∑ i ∈ S, hf i / 2 * rf i) =
      ∑ i ∈ S, if cut i then H i / 2 * R i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : cut i <;> simp [hf, rf, h]
  have hr : (∑ i ∈ S, |rf i|) =
      ∑ i ∈ S, if cut i then |R i| else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : cut i <;> simp [rf, h]
  simpa only [heq, hr] using hSum
