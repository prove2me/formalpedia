-- Prove2me | solution 1 for FeasibleBasesHC.Structure.Supplement.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:28:05.046856+00:00
-- url     : https://prove2.me/submissions/35a9e157-e6f4-47e4-ba38-b8e3a448cbc1

import Mathlib
import Definitions.Def_FeasibleBasesHC_Structure_Supplement_Counts

open FeasibleBasesHC
open FeasibleBasesHC.Structure
open FeasibleBasesHC.Structure.Supplement

theorem solution {n : ℕ} [NeZero n] (q : Quadruple n)
    (hpi : q.pi q.s ∈ q.U) (hprev : q.s - 1 ∈ R n ∪ q.U) :
    (W q q.U q.L).card + (W q q.U (R n)).card + (W q (R n) q.L).card =
      (W q q.L q.U).card + 1 := by
        classical
        have hpart (i : Fin n) : i ∈ q.L ∨ i ∈ q.U ↔ i ≠ 0 ∧ i ≠ q.s := by
          have := Finset.ext_iff.mp q.partition i
          simpa using this
        have hL0 : (0 : Fin n) ∉ q.L := by
          intro h
          exact (hpart 0 |>.mp (Or.inl h)).1 rfl
        have hU0 : (0 : Fin n) ∉ q.U := by
          intro h
          exact (hpart 0 |>.mp (Or.inr h)).1 rfl
        have hLs : q.s ∉ q.L := by
          intro h
          exact (hpart q.s |>.mp (Or.inl h)).2 rfl
        have hdis (i : Fin n) (hl : i ∈ q.L) (hu : i ∈ q.U) : False :=
          Finset.disjoint_left.mp q.disjoint hl hu
        have htL : q.s - 1 ∉ q.L := by
          intro h
          rcases Finset.mem_union.mp hprev with ht | ht
          · have ht0 : q.s - 1 = 0 := by simpa [R] using ht
            exact hL0 (ht0 ▸ h)
          · exact hdis _ h ht
        have hts : q.pi (q.s - 1) = q.s := by
          have := (q.successor_iff (q.s - 1)).mpr rfl
          simpa using this
        have hmem (P Q : Finset (Fin n)) (i : Fin n) :
            i ∈ W q P Q ↔ i ≠ q.s ∧ i ≠ q.s - 1 ∧ i ∈ P ∧ q.pi i ∈ Q := by
          simp [W, active, and_assoc]
        have hLactive (i : Fin n) (hi : i ∈ q.L) : i ≠ q.s ∧ i ≠ q.s - 1 := by
          constructor
          · rintro rfl; exact hLs hi
          · rintro rfl; exact htL hi
        have hLimage (i : Fin n) (hi : i ∈ q.L) : q.pi i ≠ q.s := by
          intro he
          have : i = q.s - 1 := q.pi.injective (he.trans hts.symm)
          exact htL (this ▸ hi)
        have hpreactive (i : Fin n) (hi : q.pi i ∈ q.L ∨ q.pi i = 0) :
            i ≠ q.s ∧ i ≠ q.s - 1 := by
          constructor
          · rintro rfl
            rcases hi with hi | hi
            · exact hdis _ hi hpi
            · exact hU0 (hi ▸ hpi)
          · rintro rfl
            rw [hts] at hi
            rcases hi with hi | hi
            · exact hLs hi
            · exact q.s_ne_root hi
        have hclass (i : Fin n) (his : i ≠ q.s) : i ∈ q.L ∨ i ∈ q.U ∨ i ∈ R n := by
          by_cases hi0 : i = 0
          · exact Or.inr (Or.inr (by simp [R, hi0]))
          · rcases (hpart i).mpr ⟨hi0, his⟩ with hi | hi
            · exact Or.inl hi
            · exact Or.inr (Or.inl hi)
        have hrow : W q q.L q.L ∪ W q q.L q.U ∪ W q q.L (R n) = q.L := by
          ext i
          simp only [Finset.mem_union, hmem]
          constructor
          · rintro ((hi | hi) | hi) <;> exact hi.2.2.1
          · intro hi
            have ha := hLactive i hi
            rcases hclass (q.pi i) (hLimage i hi) with hp | hp | hp
            · exact Or.inl (Or.inl ⟨ha.1, ha.2, hi, hp⟩)
            · exact Or.inl (Or.inr ⟨ha.1, ha.2, hi, hp⟩)
            · exact Or.inr ⟨ha.1, ha.2, hi, hp⟩
        have hcol : W q q.L q.L ∪ W q q.U q.L ∪ W q (R n) q.L =
            Finset.univ.filter (fun i => q.pi i ∈ q.L) := by
          ext i
          simp only [Finset.mem_union, hmem, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ((hi | hi) | hi) <;> exact hi.2.2.2
          · intro hi
            have ha := hpreactive i (Or.inl hi)
            rcases hclass i ha.1 with hp | hp | hp
            · exact Or.inl (Or.inl ⟨ha.1, ha.2, hp, hi⟩)
            · exact Or.inl (Or.inr ⟨ha.1, ha.2, hp, hi⟩)
            · exact Or.inr ⟨ha.1, ha.2, hp, hi⟩
        have hroot : W q q.L (R n) ∪ W q q.U (R n) = {q.pi.symm 0} := by
          ext i
          simp only [Finset.mem_union, hmem, R, Finset.mem_singleton]
          constructor
          · rintro (hi | hi) <;> exact q.pi.injective (by simpa using hi.2.2.2)
          · intro hi
            have hz : q.pi i = 0 := by simp [hi]
            have ha := hpreactive i (Or.inr hz)
            have hi0 : i ≠ 0 := by
              rintro rfl
              exact q.fixedPointFree 0 hz
            rcases (hpart i).mpr ⟨hi0, ha.1⟩ with hp | hp
            · exact Or.inl ⟨ha.1, ha.2, hp, hz⟩
            · exact Or.inr ⟨ha.1, ha.2, hp, hz⟩
        have hcardcol : (Finset.univ.filter (fun i => q.pi i ∈ q.L)).card = q.L.card := by
          apply Finset.card_bij (fun i _ => q.pi i)
          · simp
          · intro a ha b hb he
            exact q.pi.injective he
          · intro b hb
            refine ⟨q.pi.symm b, ?_, by simp⟩
            simpa using hb
        have hWdisQ (P Q T : Finset (Fin n)) (hd : Disjoint Q T) :
            Disjoint (W q P Q) (W q P T) := by
          apply Finset.disjoint_left.mpr
          intro i hi hj
          exact Finset.disjoint_left.mp hd (hmem P Q i |>.mp hi).2.2.2
            (hmem P T i |>.mp hj).2.2.2
        have hWdisP (P Q T : Finset (Fin n)) (hd : Disjoint P Q) :
            Disjoint (W q P T) (W q Q T) := by
          apply Finset.disjoint_left.mpr
          intro i hi hj
          exact Finset.disjoint_left.mp hd (hmem P T i |>.mp hi).2.2.1
            (hmem Q T i |>.mp hj).2.2.1
        have hLR : Disjoint q.L (R n) := by simpa [R] using hL0
        have hUR : Disjoint q.U (R n) := by simpa [R] using hU0
        have hr := congrArg Finset.card hrow
        have hc := (congrArg Finset.card hcol).trans hcardcol
        have hz := congrArg Finset.card hroot
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
            ⟨hWdisQ _ _ _ hLR, hWdisQ _ _ _ hUR⟩),
            Finset.card_union_of_disjoint (hWdisQ _ _ _ q.disjoint)] at hr
        rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr
            ⟨hWdisP _ _ _ hLR, hWdisP _ _ _ hUR⟩),
            Finset.card_union_of_disjoint (hWdisP _ _ _ q.disjoint)] at hc
        rw [Finset.card_union_of_disjoint (hWdisP _ _ _ q.disjoint), Finset.card_singleton] at hz
        omega
