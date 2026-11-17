-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_disjoint_finite_grid_occupied_mismatch_forces_double_cell_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:31:49.967285+00:00
-- url     : https://prove2.me/submissions/d1a9cc5b-976d-44c4-9a2a-4ecb1e38b54b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset Set AvramDividend.Classical
noncomputable section
theorem solution
    {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (I : Finset ι) (S : Finset α) (F : ι → Finset α)
    (hCover : I.biUnion F = S)
    (hDisjoint : (I : Set ι).PairwiseDisjoint F)
    (hBad : S.card ≠ (I.filter (fun i => (F i).Nonempty)).card) :
    ∃ i ∈ I, 2 ≤ (F i).card := by
  classical
  by_contra h
  have hSingle : ∀ i ∈ I, (F i).card ≤ 1 := by
    intro i hi
    by_contra hh
    have hn : 2 ≤ (F i).card := by omega
    exact h ⟨i, hi, hn⟩
  have hCard := avram_a26_finite_disjoint_singleton_partition_occupied_card_20261116
    I F hDisjoint hSingle
  exact hBad (by rw [← hCover]; exact hCard)
