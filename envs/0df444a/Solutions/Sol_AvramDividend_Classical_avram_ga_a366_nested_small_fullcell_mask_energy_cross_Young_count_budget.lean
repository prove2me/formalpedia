-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a366_nested_small_fullcell_mask_energy_cross_Young_count_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:10:44.350971+00:00
-- url     : https://prove2.me/submissions/52b5acdd-be77-4083-be2b-94b9f31b12b6

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {ι : Type*} (S : Finset ι)
    (A B : ι → Prop) [∀ i, Decidable (A i)]
    [∀ i, Decidable (B i)]
    (a b : ι → ℝ) (c : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : 0 ≤ c)
    (hMask : ∀ i, A i → B i) :
    (∑ i ∈ S, if A i then a i + b i + c else 0) ≤
      (∑ i ∈ S, if B i then a i else 0) +
      (∑ i ∈ S, if B i then b i else 0) +
        (S.card : ℝ) * c := by
  classical
  have hCell (i : ι) :
      (if A i then a i + b i + c else 0) ≤
      (if B i then a i else 0) +
        (if B i then b i else 0) + c := by
    by_cases hA : A i
    · have hB := hMask i hA
      simp [hA,hB]
    · by_cases hB : B i
      · simp only [if_neg hA, if_pos hB]
        linarith [ha i, hb i, hc]
      · simp [hA,hB,hc]
  calc
    (∑ i ∈ S, if A i then a i + b i + c else 0) ≤
        ∑ i ∈ S, ((if B i then a i else 0) +
          (if B i then b i else 0) + c) := by
          apply Finset.sum_le_sum
          intro i _
          exact hCell i
    _ = (∑ i ∈ S, if B i then a i else 0) +
          (∑ i ∈ S, if B i then b i else 0) +
            (S.card : ℝ) * c := by
        simp only [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
