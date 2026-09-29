-- Prove2me | solution 1 for BanditAlgorithm.l1_dist_eq_two_max_event_excess
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T03:48:59.562461+00:00
-- url     : https://prove2.me/submissions/bf3ddb9c-87da-477b-ac1b-a71af8914c32

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-- **The `ℓ¹` distance as twice the largest excess of an event.**  For vectors
`p, q` with the same total mass (in particular for two probability vectors),
every event `B` satisfies `2(p(B) - q(B)) ≤ ‖p - q‖₁`, and equality is attained
at `A = {i : q i ≤ p i}`.

This is the identity `‖p - q‖₁ = 2 max_{A ⊆ S} (p(A) - q(A))` behind the
categorical concentration inequality of Exercise 38.21: an `ℓ¹` deviation of the
empirical transition vector forces a deviation of one of the `2^S` event
probabilities, each of which is a sum of independent indicators. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (hpq : ∑ i, p i = ∑ i, q i) :
    (∀ B : Finset ι, 2 * ∑ i ∈ B, (p i - q i) ≤ ∑ i, |p i - q i|)
      ∧ ∃ A : Finset ι, ∑ i, |p i - q i| = 2 * ∑ i ∈ A, (p i - q i) := by
  classical
  set A : Finset ι := Finset.univ.filter (fun i ↦ q i ≤ p i) with hA
  have hmemA : ∀ i, i ∈ A ↔ q i ≤ p i := by
    intro i; simp [hA]
  -- the total difference vanishes
  have hzero : ∑ i, (p i - q i) = 0 := by
    rw [Finset.sum_sub_distrib, hpq, sub_self]
  -- split the absolute values along `A`
  have hsplitA : ∑ i ∈ A, |p i - q i| = ∑ i ∈ A, (p i - q i) :=
    Finset.sum_congr rfl fun i hi ↦ abs_of_nonneg (by
      have := (hmemA i).mp hi; linarith)
  have hsplitAc : ∑ i ∈ Aᶜ, |p i - q i| = -∑ i ∈ Aᶜ, (p i - q i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi ↦ abs_of_nonpos ?_
    have : ¬ (q i ≤ p i) := by
      simpa [hmemA i] using (Finset.mem_compl.mp hi)
    linarith [not_le.mp this]
  have habs : ∑ i, |p i - q i| = 2 * ∑ i ∈ A, (p i - q i) := by
    have hu : ∑ i, |p i - q i| = ∑ i ∈ A, |p i - q i| + ∑ i ∈ Aᶜ, |p i - q i| :=
      (Finset.sum_add_sum_compl A _).symm
    have hd : ∑ i ∈ A, (p i - q i) + ∑ i ∈ Aᶜ, (p i - q i) = 0 := by
      rw [Finset.sum_add_sum_compl A]; exact hzero
    rw [hu, hsplitA, hsplitAc]
    linarith
  refine ⟨fun B ↦ ?_, ⟨A, habs⟩⟩
  rw [habs]
  have hstep : ∑ i ∈ B, (p i - q i) ≤ ∑ i ∈ A, (p i - q i) := by
    have hsplit : ∑ i ∈ B, (p i - q i)
        = ∑ i ∈ B ∩ A, (p i - q i) + ∑ i ∈ B \ A, (p i - q i) := by
      rw [← Finset.sum_inter_add_sum_sdiff B A]
    have h1 : ∑ i ∈ B \ A, (p i - q i) ≤ 0 := by
      refine Finset.sum_nonpos fun i hi ↦ ?_
      have : ¬ (q i ≤ p i) := by
        have := (Finset.mem_sdiff.mp hi).2
        simpa [hmemA i] using this
      linarith [not_le.mp this]
    have h2 : ∑ i ∈ B ∩ A, (p i - q i) ≤ ∑ i ∈ A, (p i - q i) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right ?_
      intro i hi _
      have := (hmemA i).mp hi
      linarith
    linarith
  linarith
