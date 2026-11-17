-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:10:29.683619+00:00
-- url     : https://prove2.me/submissions/064f3389-2d9a-40ca-aea0-9506a5476d7e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset Set
open scoped BigOperators
noncomputable section
theorem solution
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (F : ι → Finset α)
    (hDisjoint : (I : Set ι).PairwiseDisjoint F)
    (hSingle : ∀ i ∈ I, (F i).card ≤ 1) :
    (I.biUnion F).card =
      (I.filter (fun i => (F i).Nonempty)).card := by
  classical
  rw [Finset.card_biUnion hDisjoint, Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hne : (F i).Nonempty
  · have hp : 0 < (F i).card := Finset.card_pos.mpr hne
    have hone : (F i).card = 1 := by
      have hle := hSingle i hi
      omega
    simp [hne, hone]
  · have hz : (F i).card = 0 := by
      by_contra hzero
      exact hne (Finset.card_pos.mp (Nat.pos_of_ne_zero hzero))
    simp [hne, hz]
