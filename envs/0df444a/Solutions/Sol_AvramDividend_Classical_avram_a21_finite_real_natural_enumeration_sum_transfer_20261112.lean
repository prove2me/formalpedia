-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_finite_real_natural_enumeration_sum_transfer_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:18:00.568803+00:00
-- url     : https://prove2.me/submissions/02e06928-52d4-4133-a0a1-604ca11bcfa9

import Mathlib
import Mathlib.Data.Finset.Card
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
noncomputable section

/-- A faithful natural-index enumeration preserves every real finite sum. -/
theorem solution
    (s : Finset ℝ) (u : ℕ → ℝ)
    (hu : ∀ i ∈ Finset.range s.card, u i ∈ s)
    (hinj : ∀ i ∈ Finset.range s.card,
      ∀ j ∈ Finset.range s.card, i ≠ j → u i ≠ u j)
    (hsurj : ∀ y ∈ s, ∃ i ∈ Finset.range s.card, u i = y)
    (w : ℝ → ℝ) :
    (∑ i ∈ Finset.range s.card, w (u i)) =
      ∑ y ∈ s, w y := by
  classical
  apply Finset.sum_bij (fun i hi => u i)
  · intro i hi
    exact hu i hi
  · intro i hi j hj he
    by_contra hij
    exact (hinj i hi j hj hij) he
  · intro y hy
    obtain ⟨i, hi, he⟩ := hsurj y hy
    exact ⟨i, hi, he⟩
  · intro i hi
    rfl
