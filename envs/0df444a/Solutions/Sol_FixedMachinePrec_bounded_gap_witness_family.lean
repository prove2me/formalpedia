-- Prove2me | solution 1 for FixedMachinePrec.bounded_gap_witness_family
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:00:16.418824+00:00
-- url     : https://prove2.me/submissions/4de9e34c-4391-4fc6-a8ab-b11ec4ed701d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula
import Definitions.Def_FixedMachinePrec_Hierarchy
import Theorems.Thm_FixedMachinePrec_large_gap_witness_domains

open FixedMachinePrec


theorem solution {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 3 ≤ m) (hp : IsStrictOrder' prec) (rank : Fin N → ℕ) (hr : IsTopoRank prec rank)
    (hf : ∃ S, IsFullSchedule prec m Finset.univ S) :
    let F := family prec rank m (4*m+5)
    let C := family prec rank m (m+3)
    ∃ D : Finset (Finset (Fin N)), Finset.univ ∈ D ∧ D ⊆ F ∧
      ∀ W ∈ D, W.Nonempty → ∃ S marks, IsFullSchedule prec m W S ∧ marks ≠ [] ∧
        marks.Pairwise (· < ·) ∧ (∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length) ∧
        (∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X) ∧
        ∀ A ∈ gaps S marks, A.Nonempty → A ∈ D ∧ A.card < W.card := by
  classical
  let F := family prec rank m (4*m+5)
  let C := family prec rank m (m+3)
  let terminal := (Finset.univ : Finset (Finset (Fin N))).filter fun A => A.card = m ∧ IsAntichainSet prec A
  obtain ⟨D,hroot,hF,step⟩ := large_gap_witness_domains m prec hm hp rank hr hf
  have atom (K) (a : Atom N) (h : a.Valid m) (hk : 1 ≤ K) : a.eval prec rank ∈ family prec rank m K := by
    simp only [family,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨.atom a,h,hk,rfl⟩
  have small {A} (ha : A ∈ terminal) : A.card = m ∧ IsAntichainSet prec A := (Finset.mem_filter.mp ha).2
  refine ⟨(D.filter (fun W => m < W.card)) ∪ terminal ∪ {∅},?_,?_,?_⟩
  · by_cases big : m < N
    · simp [hroot big,big]
    · obtain ⟨L,hs⟩ := hf
      cases L with
      | nil => have e := hs.2.2.1; simp at e; simp [← e]
      | cons A tail =>
        obtain ⟨hcard,hanti⟩ := hs.1 A (by simp)
        have eq : A = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp;omega)
        subst A; simp [terminal,hcard,IsAntichainSet,hanti]
  · intro A hA
    rcases Finset.mem_union.mp hA with h | h
    · rcases Finset.mem_union.mp h with hd | ht
      · exact hF (Finset.mem_filter.mp hd).1
      · exact atom _ (.boundary A) (small ht).1 (by omega)
    · obtain rfl := Finset.mem_singleton.mp h
      exact atom _ .empty trivial (by omega)
  · intro W hW hn
    rcases Finset.mem_union.mp hW with h | e
    · rcases Finset.mem_union.mp h with hd | ht
      · obtain ⟨S,marks,hs,hk,hi,hr,hc,hg⟩ := step W (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hd).2
        refine ⟨S,marks,hs,hk,hi,hr,hc,?_⟩
        intro A ha hne
        rcases hg A ha hne with ⟨hD,hbig,hlt⟩ | hsmall
        · exact ⟨by simp [hD,hbig],hlt⟩
        · exact ⟨by simp [terminal,hsmall],hsmall.1 ▸ (Finset.mem_filter.mp hd).2⟩
      · obtain ⟨hcard,anti⟩ := small ht
        refine ⟨[W],[1],?_,by simp,by simp,by simp,?_,?_⟩
        · refine ⟨by simpa [IsAntichainSet] using And.intro hcard anti,by simp,by simp,?_⟩
          intro i j hi hj x y hx hy hxy
          simp only [List.length_singleton] at hi hj
          obtain rfl : i = 0 := by omega
          obtain rfl : j = 0 := by omega
          exact False.elim (anti x hx y hy hxy)
        · intro t ht; obtain rfl := List.mem_singleton.mp ht
          exact ⟨∅,atom _ .empty trivial (by omega),by simp [slotsBetween]⟩
        · simp [gaps,slotsBetween]
    · exact False.elim (hn.ne_empty (Finset.mem_singleton.mp e))
