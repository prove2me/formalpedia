-- Prove2me | solution 1 for Erdos9796Mission_four_pair_overlap_on_seven
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-07T21:34:37.402717+00:00
-- url     : https://prove2.me/submissions/5c87cdab-352e-4ae6-9230-9fac843c8f38

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib.Data.Finset.Card
set_option autoImplicit false

/-! Standalone proof of four-support overlap inside a seven-element carrier. -/

theorem solution {α : Type*} [DecidableEq α]
    (U A B C D : Finset α) (hU : U.card ≤ 7)
    (hAU : A ⊆ U) (hBU : B ⊆ U) (hCU : C ⊆ U) (hDU : D ⊆ U)
    (hA : A.card = 2) (hB : B.card = 2) (hC : C.card = 2) (hD : D.card = 2)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hCD : Disjoint C D) :
    (A ∩ D).Nonempty ∨ (B ∩ C).Nonempty ∨ (B ∩ D).Nonempty := by
  classical
  by_contra h
  have hAD : Disjoint A D := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxD
    exact h (Or.inl ⟨x, Finset.mem_inter.mpr ⟨hxA, hxD⟩⟩)
  have hBC : Disjoint B C := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxC
    exact h (Or.inr (Or.inl ⟨x, Finset.mem_inter.mpr ⟨hxB, hxC⟩⟩))
  have hBD : Disjoint B D := by
    apply Finset.disjoint_left.mpr
    intro x hxB hxD
    exact h (Or.inr (Or.inr ⟨x, Finset.mem_inter.mpr ⟨hxB, hxD⟩⟩))
  have hABCD : Disjoint (A ∪ B) (C ∪ D) := by
    apply Finset.disjoint_left.mpr
    intro x hxAB hxCD
    rcases Finset.mem_union.mp hxAB with hxA | hxB
    · rcases Finset.mem_union.mp hxCD with hxC | hxD
      · exact Finset.disjoint_left.mp hAC hxA hxC
      · exact Finset.disjoint_left.mp hAD hxA hxD
    · rcases Finset.mem_union.mp hxCD with hxC | hxD
      · exact Finset.disjoint_left.mp hBC hxB hxC
      · exact Finset.disjoint_left.mp hBD hxB hxD
  have hcard : ((A ∪ B) ∪ (C ∪ D)).card = 8 := by
    rw [Finset.card_union_of_disjoint hABCD, Finset.card_union_of_disjoint hAB,
      Finset.card_union_of_disjoint hCD, hA, hB, hC, hD]
  have hsub : (A ∪ B) ∪ (C ∪ D) ⊆ U :=
    Finset.union_subset (Finset.union_subset hAU hBU) (Finset.union_subset hCU hDU)
  have hle : 8 ≤ U.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  exact (by decide : ¬ (8 : ℕ) ≤ 7) (hle.trans hU)
