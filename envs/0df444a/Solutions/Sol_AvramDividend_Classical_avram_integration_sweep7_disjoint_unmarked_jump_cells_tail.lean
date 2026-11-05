-- Prove2me | solution 1 for AvramDividend.Classical.avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:31:54.133886+00:00
-- url     : https://prove2.me/submissions/5e753497-bb67-46df-b262-370cf1ffe735

import Mathlib.Analysis.Normed.Group.InfiniteSum
open Filter Set
open scoped BigOperators Classical
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {ι : Type*} (j : ι → ℝ)
    (hj : Summable j) (hjnonneg : ∀ t, 0 ≤ j t)
    (marked : Finset ι) (cells : Finset ℕ)
    (inside : ℕ → ι → Prop)
    (hUnique : ∀ t i, i ∈ cells → ∀ k, k ∈ cells →
      inside i t → inside k t → i = k)
    (hAvoid : ∀ i, i ∈ cells → ∀ t, t ∈ marked → ¬ inside i t) :
    (∑ i ∈ cells, ∑' t, if inside i t then j t else 0) ≤
      ∑' t, if t ∈ marked then 0 else j t := by
  classical
  let f : ℕ → ι → ℝ := fun i t => if inside i t then j t else 0
  have hf (i : ℕ) : Summable (f i) := by
    apply Summable.of_norm_bounded hj
    intro t
    by_cases h : inside i t
    · simpa [f, h, Real.norm_eq_abs, abs_of_nonneg (hjnonneg t)] using (le_refl (j t))
    · simpa [f, h] using (hjnonneg t)
  have hTailSumm :
      Summable (fun t => if t ∈ marked then (0 : ℝ) else j t) := by
    apply Summable.of_norm_bounded hj
    intro t
    by_cases h : t ∈ marked
    · simpa [h] using (hjnonneg t)
    · simpa [h, Real.norm_eq_abs, abs_of_nonneg (hjnonneg t)] using (le_refl (j t))
  have hSumSumm :
      Summable (fun t => ∑ i ∈ cells, f i t) := by
    have hs : ∀ s : Finset ℕ, Summable (fun t => ∑ i ∈ s, f i t) := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
          simpa using (summable_zero : Summable (fun _ : ι => (0 : ℝ)))
      | @insert i s hi ih =>
          simpa only [Finset.sum_insert hi] using (hf i).add ih
    exact hs cells
  have hPointwise (t : ι) :
      (∑ i ∈ cells, f i t) ≤
        (if t ∈ marked then 0 else j t) := by
    by_cases ht : t ∈ marked
    · have hzero : (∑ i ∈ cells, f i t) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp [f, hAvoid i hi t ht]
      simpa [ht] using le_of_eq hzero
    · by_cases hex : ∃ i ∈ cells, inside i t
      · obtain ⟨i, hi, hci⟩ := hex
        have heq : (∑ k ∈ cells, f k t) = f i t := by
          apply Finset.sum_eq_single i
          · intro k hk hki
            have hno : ¬ inside k t := by
              intro hck
              exact hki ((hUnique t i hi k hk hci hck).symm)
            simp [f, hno]
          · intro hni
            exact False.elim (hni hi)
        simp [ht, heq, f, hci]
      · have hzero : (∑ i ∈ cells, f i t) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hno : ¬ inside i t := by
            intro h
            exact hex ⟨i, hi, h⟩
          simp [f, hno]
        simpa [ht, hzero] using hjnonneg t
  calc
    (∑ i ∈ cells, ∑' t, if inside i t then j t else 0)
        = ∑' t, ∑ i ∈ cells, f i t := by
          exact (Summable.tsum_finsetSum
            (s := cells) (f := f) (by intro i hi; exact hf i)).symm
    _ ≤ ∑' t, if t ∈ marked then 0 else j t :=
      Summable.tsum_le_tsum hPointwise hSumSumm hTailSumm
