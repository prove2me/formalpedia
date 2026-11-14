-- Prove2me | solution 1 for GenCountSampleLLL.insertion_corridor_last_family
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:59:50.057437+00:00
-- url     : https://prove2.me/submissions/f5c57544-0ce7-41d7-aa90-9b82f3ca62dd

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators
open GenCountSampleLLL

theorem solution (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (hT : T ∈ I.twoTrees D a) :
    I.DTi D a T (I.ell D a T) = D.erase a := by
  have htree : I.IsTwoTree D a T := (Finset.mem_filter.mp hT).2
  have hsub : I.N2Dc D T ⊆ D := by
    intro b hb
    simp only [Inst.N2Dc, Finset.mem_union, Finset.mem_filter] at hb
    rcases hb with ht | ⟨hd, _⟩
    · exact htree.1 ht
    · exact hd
  have ha : a ∈ I.N2Dc D T := Finset.mem_union_left _ htree.2.1
  unfold Inst.DTi Inst.ell Inst.bList Inst.DT
  simp only [List.take_length, Finset.sort_toFinset]
  ext b
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro (⟨hb, hnot⟩ | ⟨hne, hb⟩)
    · exact ⟨fun he => hnot (he ▸ ha), hb⟩
    · exact ⟨hne, hsub hb⟩
  · rintro ⟨hne, hb⟩
    by_cases ht : b ∈ I.N2Dc D T
    · exact Or.inr ⟨hne, ht⟩
    · exact Or.inl ⟨hb, ht⟩

