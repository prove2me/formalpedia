-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_occupied_grid_card_le_source_finset_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:08:00.192192+00:00
-- url     : https://prove2.me/submissions/d6176b60-0732-4983-8c26-c0d6dbaa6a1a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Occupied time cells never outnumber actual marked source jump times. -/
theorem solution
    (F : Finset ℝ≥0) (I : Finset ℕ)
    (R : ℝ≥0 → ℕ → Prop)
    (A : Finset ℕ)
    (hA : ∀ i, i ∈ A ↔ i ∈ I ∧ ∃ u ∈ F, R u i)
    (hIndexUnique : ∀ u ∈ F, ∀ i ∈ I, ∀ j ∈ I,
      R u i → R u j → i = j) :
    A.card ≤ F.card := by
  classical
  have hWitness (i : ℕ) (hi : i ∈ A) : ∃ u ∈ F, R u i :=
    ((hA i).mp hi).2
  let f : ℕ → ℝ≥0 := fun i =>
    if hi : i ∈ A then Classical.choose (hWitness i hi) else 0
  have hf (i : ℕ) (hi : i ∈ A) :
      f i ∈ F ∧ R (f i) i := by
    simpa only [f, dif_pos hi] using
      (Classical.choose_spec (hWitness i hi))
  change A.card ≤ F.card
  apply Finset.card_le_card_of_injOn f
  · intro i hi
    exact (hf i hi).1
  · intro i hi j hj heq
    have hrel : R (f i) j := by
      simpa only [heq] using (hf j hj).2
    exact hIndexUnique (f i) (hf i hi).1 i
      ((hA i).mp hi).1 j ((hA j).mp hj).1
      (hf i hi).2 hrel
