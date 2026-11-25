-- Prove2me | solution 1 for DegreeSequences.exists_switch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:54.68793+00:00
-- url     : https://prove2.me/submissions/95475d11-b84c-483f-8a8c-53b6dcf38009

module
public import Mathlib
public import Definitions.Def_DegreeSeqLib_DegreeSequences
public import Theorems.Thm_DegreeSequences_degree_editGraph

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open DegreeSequences
namespace DegreeSequences
theorem _root_.solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a i k : V) (hai : a ≠ i) (hdeg : G.degree k ≤ G.degree i)
    (hai' : ¬ G.Adj a i) (hak : G.Adj a k) :
    ∃ (G' : SimpleGraph V) (_ : DecidableRel G'.Adj), (∀ v, G'.degree v = G.degree v) ∧
      ∀ v, (G'.Adj a v ↔ (v ≠ k ∧ G.Adj a v) ∨ v = i) := by
  classical
  have hik : i ≠ k := fun h => hai' (h ▸ hak)
  have hak' : a ≠ k := hak.ne
  have hia : ¬ G.Adj i a := fun h => hai' h.symm
  obtain ⟨w, hiw, hkw, hwk⟩ : ∃ w, G.Adj i w ∧ ¬ G.Adj k w ∧ w ≠ k := by
    by_contra hcon
    push Not at hcon
    by_cases hik' : G.Adj i k
    · have hsub : (G.neighborFinset i).erase k ⊆ ((G.neighborFinset k).erase a).erase i := by
        intro w hw
        simp only [mem_erase, mem_neighborFinset] at hw ⊢
        refine ⟨fun h => ?_, fun h => ?_, ?_⟩
        · subst h; exact G.loopless.irrefl _ hw.2
        · subst h; exact hia hw.2
        · by_contra h; exact hw.1 (hcon w hw.2 h)
      have h1 := card_le_card hsub
      have h2 : a ∈ G.neighborFinset k := by simpa using hak.symm
      have h3 : i ∈ (G.neighborFinset k).erase a := by simpa using ⟨hai.symm, hik'.symm⟩
      have h4 : k ∈ G.neighborFinset i := by simpa using hik'
      rw [card_erase_of_mem h4, card_erase_of_mem h3, card_erase_of_mem h2,
        card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at h1
      have h5 : 0 < G.degree i := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨k, h4⟩
      have h6 : 1 < G.degree k := by
        rw [← card_neighborFinset_eq_degree]
        exact one_lt_card.mpr ⟨a, h2, i, (mem_erase.mp h3).2, hai⟩
      omega
    · have hsub : G.neighborFinset i ⊆ (G.neighborFinset k).erase a := by
        intro w hw
        simp only [mem_erase, mem_neighborFinset] at hw ⊢
        refine ⟨fun h => ?_, ?_⟩
        · subst h; exact hia hw
        · by_contra h; exact hik' (hcon w hw h ▸ hw)
      have h1 := card_le_card hsub
      have h2 : a ∈ G.neighborFinset k := by simpa using hak.symm
      rw [card_erase_of_mem h2, card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree] at h1
      have h6 : 0 < G.degree k := by
        rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨a, h2⟩
      omega
  have hiw' : i ≠ w := hiw.ne
  have haw : a ≠ w := fun h => hai' (h ▸ hiw.symm)
  set R : Finset (Sym2 V) := {s(a, k), s(i, w)} with hRdef
  set A : Finset (Sym2 V) := {s(a, i), s(k, w)} with hAdef
  have hR : ∀ e ∈ R, e ∈ G.edgeSet := by
    simp [hRdef, hak, hiw]
  have hA : ∀ e ∈ A, e ∉ G.edgeSet ∧ ¬ e.IsDiag := by
    simp [hAdef, hai', hkw, hai, hwk.symm]
  refine ⟨editGraph G R A, inferInstance, fun v => ?_, fun v => ?_⟩
  · have key := degree_editGraph G R A hR hA v
    have hne1 : s(a, k) ≠ s(i, w) := by simp [hai, haw]
    have hne2 : s(a, i) ≠ s(k, w) := by simp [hak', haw]
    rw [hRdef, hAdef, sum_pair hne1, sum_pair hne2] at key
    simp only [Sym2.mem_iff] at key
    by_cases h1 : v = a
    · subst h1; simp [hak', hai, haw] at key; omega
    by_cases h2 : v = k
    · subst h2; simp [hak'.symm, hik.symm, hwk.symm] at key; omega
    by_cases h3 : v = i
    · subst h3; simp [hai.symm, hik, hiw'] at key; omega
    by_cases h4 : v = w
    · subst h4; simp [haw.symm, hiw'.symm, hwk] at key; omega
    simp [h1, h2, h3, h4] at key; omega
  · simp only [editGraph, hRdef, hAdef, mem_insert, mem_singleton, Sym2.eq_iff, true_and,
      hai, hak', haw, false_and, or_false, ne_eq]
    constructor
    · rintro ⟨-, ⟨h1, h2⟩ | h⟩
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | rfl)
      · exact ⟨h2.ne, Or.inl ⟨h2, h1⟩⟩
      · exact ⟨hai, Or.inr rfl⟩
end DegreeSequences
