-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_simple_mark_natural_fibre_partition_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:34:53.887334+00:00
-- url     : https://prove2.me/submissions/9d595b89-a856-45a5-aa95-894e9e8d4364

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_fibre_nat_enumeration_20261112
import Theorems.Thm_AvramDividend_Classical_avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- A real Borel simple mark has a faithful natural-number-indexed
partition, with exact preservation of all finite weighted sums. -/
theorem solution
    (S : Set ℝ) (hS : MeasurableSet S)
    (f : SimpleFunc ℝ ℝ) :
    ∃ (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ),
      (∀ i ∈ Finset.range K,
        MeasurableSet (B i) ∧ B i ⊆ S) ∧
      (∀ i ∈ Finset.range K,
        ∀ j ∈ Finset.range K, i ≠ j → Disjoint (B i) (B j)) ∧
      (∀ w : ℝ → ℝ,
        (∑ i ∈ Finset.range K, w (c i)) = ∑ y ∈ f.range, w y) ∧
      (∀ i ∈ Finset.range K, B i = S ∩ f ⁻¹' {c i}) := by
  classical
  obtain ⟨u, hu, hinj, hsurj⟩ :=
    avram_a21_finite_real_fibre_nat_enumeration_20261112 f.range
  let B : ℕ → Set ℝ := fun i => S ∩ f ⁻¹' {u i}
  refine ⟨f.range.card, B, u, ?_, ?_, ?_, ?_⟩
  · intro i hi
    constructor
    · exact hS.inter ((measurableSet_singleton (u i)).preimage f.measurable)
    · intro z hz
      exact hz.1
  · intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    exact (hinj i hi j hj hij) (hzi.2.symm.trans hzj.2)
  · intro w
    exact avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
      f.range u hu hinj hsurj w
  · intro i hi
    rfl
